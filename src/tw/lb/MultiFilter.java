package tw.lb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Random;
import java.util.Set;
import java.util.Stack;

import log.Log;
import tw.common.Edge;
import tw.common.Graph;
import tw.common.LocalGraph;
import tw.common.XBitSet;
import tw.common.Minor;
import tw.common.TreeDecomposition;
import tw.decomposer.SemiPID;
import tw.decomposer.SemiPIDFull;
import tw.acsd.ACSDecomposition;

public class MultiFilter {
  static final boolean VERBOSE = true;
//  static final boolean VERBOSE = false;
  static final boolean TRACE = true;
//  static final boolean TRACE = false;
//  static final boolean VERIFY = true;

  static final int BASE_SIZE = 70;
  static final int N_FILTERS = 10;
  static final int UNC_CHUNK = 10;
  static final int N_TRY = 10;
  static final String VERSION = "3";

  Graph g;
  public int lb;
  public Minor obs;
  
  Contractor baseCont;
  
  Edge[] contracted;
  
  Filter[] filters;
  Edge[] fillable;
  
  Contractor[] bestContractor;

  Random random;

  static long t0;
  

  static Log log;

  public MultiFilter(Graph g) {
    this.g = g;
    random = new Random(1);
  }
  
  public int initialLowerBound() {
    ContractionLB clb = new ContractionLB(g);
    lb = clb.lowerbound();

    Minor minor = clb.boundingMinor;
    if (VERBOSE) {
      log.log("minor of " + minor.m + " vertices " + ", width = " + lb + ", " + (System.currentTimeMillis() - t0)
          + " millisecs");
      log.log(minor.toString());
    }

    obs = deriveObstruction(minor);
    
    TreeDecomposition td = SemiPID.decompose(obs.getGraph());
    assert td.width == lb;
    return lb;
  }
  
  public int improvedLowerBound() {
    Minor newObs = improve();
    if (newObs != null) {
      lb = SemiPID.decompose(newObs.getGraph()).width;
      obs = newObs;
      return lb;
    } else
      return -1;
  }

  Minor improve() {
    contracted = obs.contractionEdges();
    int nCont = contracted.length;
    if (g.n - nCont == lb + 1) {
      // the obstruction is a clique;
      nCont--;
    }

    baseCont = new Contractor(XBitSet.all(nCont));
    
    listFillabels();
    
    if (TRACE) {
      System.out.println("fillables: " + Arrays.deepToString(fillable));
    }
    
    filters = new Filter[N_FILTERS];
    for (int i = 0; i < N_FILTERS; i++) {
      filters[i] = new Filter();
    }
    
    if (TRACE) {
      System.out.println("filters:");
      for (int i = 0; i < N_FILTERS; i++) {
        System.out.println(i + ": " + filters[i]);
      }
    }
    
    baseCont.score();
    
    Contractor current = baseCont;
    
    while (!current.clears(g)) {
      if (TRACE) {
        System.out.println("current " + current);
      }
      current = current.improve();
      if (TRACE) {
        System.out.println("impreoved to " + current);
      }
      current.shrinkFilters();
      if (TRACE) {
        System.out.println("filters shrunk to: ");
        for (Filter filter: filters) {
          System.out.println(" " + filter);
        }
      }

      current = current.maximalize();
    }
    return deriveObstruction(current.contract(g));
  }
  
  ArrayList<Contractor> listBests() {
    ArrayList<Contractor> result = new ArrayList<>();
    Contractor prev = null;
    for (int i = g.n - BASE_SIZE; i <= baseCont.nCont; i++) {
      Contractor cont = bestContractor[i];
      if (cont != prev) {
        result.add(cont);
        prev = cont;
      }
    }
    return result;
  }

  void listFillabels() {
    Minor minor = baseCont.contract(g);
    Graph h = minor.getGraph();
    ArrayList<Edge> fillablesList = new ArrayList<>();
    for (int v = 0; v < h.n; v++) {
      XBitSet nnb = h.all.subtract(h.neighborSet[v]);
      for (int w = nnb.nextSetBit(v + 1); w >= 0; w = nnb.nextSetBit(w + 1)) {
        int vg = randomSetBit(minor.components[v]);
        int wg = randomSetBit(minor.components[w]);
        assert !g.areAdjacent(vg, wg);
        Edge e = new Edge(vg, wg, g.n);
        fillablesList.add(e);
      }
    }
    fillable = new Edge[fillablesList.size()];
    fillablesList.toArray(fillable);
  }

  int randomSetBit(XBitSet s) {
    int[] a = s.toArray();
    return a[random.nextInt(a.length)];
  }
  
  Minor deriveObstruction(Minor minor) {
    Graph h = minor.getGraph();
    int k = SemiPID.decompose(h).width;
  
    Set<Edge> uncontractables = new HashSet<>();
    Minor mm = minor;
    
    while (true) {
      h = mm.getGraph();
      assert !isFeasible(h, k - 1);

      if (h.n == k + 1) {
        assert h.isClique(h.all);
        return mm;
      }

      ArrayList<Edge> edges = new ArrayList<>();
      for (int v = 0; v < h.n; v++) {
        XBitSet nb = h.neighborSet[v];
        for (int w = nb.nextSetBit(v + 1); w >= 0; w = nb.nextSetBit(w + 1)) {
          Edge e = originalEdge(v, w, mm);
          if (!uncontractables.contains(e)) {
            edges.add(e);
          }
        }
      }

//      if (VERBOSE) {
//        log.log(edges.size() + " candidate edges for contraction, n = " + h.n);
//      }

      Minor mm1 = null;
      for (Edge e : edges) {
        mm1 = mm.contract(mm.map[e.u], mm.map[e.v]);
        if (!isFeasible(mm1.getGraph(), k - 1)) {
          break;
        }
        else {
          uncontractables.add(e);
          mm1 = null;
        }
      }
      if (mm1 != null) {
        mm = mm1;
      }
      else {
        return mm;
      }
    }
  }
  
  XBitSet randomSubset(XBitSet set, int k) {
    XBitSet result = new XBitSet();
    int n = set.cardinality();
    int j = k;
    for (int i = set.nextSetBit(0); i >= 0; i = set.nextSetBit(i+1)) {
      if (random.nextInt(n) < j) {
        result.set(i);
        j--;
      }
      n--;
    }
    return result; 
  }

  Edge originalEdge(int u, int v, Minor minor) {
    XBitSet vs1 = minor.components[u];
    XBitSet vs2 = minor.components[v];
    for (int w = vs1.nextSetBit(0); w >= 0; w = vs1.nextSetBit(w + 1)) {
      XBitSet nb = minor.g.neighborSet[w].intersectWith(vs2);
      if (!nb.isEmpty()) {
        return new Edge(w, nb.nextSetBit(0), minor.g.n);
      }
    }
    assert false;
    return null;
  }

  String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }

  boolean isFeasible(Graph h, int k) {
    if (h.n <= k + 1) {
      return true;
    }
    SemiPID spid = new SemiPID(h, k, false);
    boolean isFeasible = spid.isFeasible();
    if (TRACE) {
      SemiPIDFull spidfull = new SemiPIDFull(h, k);
      spidfull.computeSafeSeps();
      assert isFeasible == !spidfull.safeSeps.isEmpty();
    }
    return spid.isFeasible();
  }

  class Contractor implements Comparable<Contractor> {
    XBitSet contSet;
    int nCont;
    int score;
    int[] sca;
    int nSS;
    
    Contractor(XBitSet contSet) {
      this.contSet = contSet;
      nCont = contSet.cardinality();
    }
    
    Contractor maximalize() {
      XBitSet rem = baseCont.contSet.subtract(contSet);
      Contractor cont = this;
      boolean moving = true;
      while (moving) {
        moving = false;
        for (int i = rem.nextSetBit(0); i >= 0; i = rem.nextSetBit(i + 1)) {
          rem.clear(i);
          Contractor cont1 = new Contractor(cont.contSet.addBit(i));
          if (cont1.clearAllFilters()) {
            cont = cont1;
            moving = true;
          }
        }
      }
      return cont;
    }

    boolean clearAllFilters() {
      for (Filter filter: filters) {
        if (!filter.clearedBy(this)) {
          return false;
        }
      }
      return true;
    }

    void shrinkFilters() {
      for (Filter filter: filters) {
        filter.shrinkFor(this);
      }
    }

    int graphSize() {
      return g.n - nCont;
    }
    
    Contractor improve() {
      if (TRACE) {
        System.out.println("improving " + this);
      }
      Contractor cont = this;
      while (cont.allFiltersTight()) {
        cont = cont.bestUncontraction();
        if (TRACE) {
          System.out.println("best uncont " + cont);
        }
      }
      return cont;
    }

    Contractor bestUncontraction() {
      Contractor best = null;
      for (int i = contSet.nextSetBit(0); i >= 0; i = contSet.nextSetBit(i + 1)) {
        Contractor cont = new Contractor(contSet.removeBit(i));
        cont.score();
        if (best == null || cont.score < best.score) {
          best = cont;
        }
      }
      return best;
    }

    boolean allFiltersTight() {
      for (Filter filter: filters) {
        if (!filter.isTightFor(this)) {
          return false;
        }
      }
      return true;
  }

    boolean clears(Graph g) {
      Minor minor = contract(g);
      return !isFeasible(minor.h, lb);
    }

    void score() {
      score = 0;
      sca = new int[N_FILTERS];
      for (int i = 0; i < N_FILTERS; i++) {
        sca[i] = filters[i].score(this);
        score += sca[i];
      }
    }
    
    void computeNSS() {
      Minor minor = contract(g);
      Graph h = minor.getGraph();
      SemiPIDFull spidfull = new SemiPIDFull(h, lb);
      spidfull.computeSafeSeps();
      nSS = spidfull.safeSeps.size();      
    }
    
    Minor contract(Graph gFilled) {
      Minor minor = new Minor(gFilled);
      for (int i = contSet.nextSetBit(0); i >= 0; i = contSet.nextSetBit(i + 1)) {
        Edge e = contracted[i];
        minor = minor.contract(minor.map[e.u], minor.map[e.v]);
      }
      return minor;
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append("score " + score + " " + Arrays.toString(sca));
      sb.append(" nCont " + nCont);
      sb.append(" graph size " + (g.n - nCont));
      sb.append(" uncont " + baseCont.contSet.subtract(contSet));
      return sb.toString();
    }
    
    @Override
    public int compareTo(Contractor cont) {
      if (score != cont.score) { 
        return score - cont.score;
      }
      if (nSS == -1) {
        computeNSS();
      }
      if (cont.nSS == -1) {
        cont.computeNSS();
      }
      if (nSS != cont.nSS) {
        return nSS - cont.nSS;
      }
      
      return - (nCont - cont.nCont);
    }
  }
  
  class Filter {
    Edge[] filled;
    int nf;
    Graph gFilled;
    Graph gFilled1;
    
    Filter() {
      super();
      ArrayList<Edge> filledEdges = new ArrayList<>();
      Minor minor = baseCont.contract(g);
      Graph hFilled = minor.getGraph();
      gFilled = g.copy();
      XBitSet xf = new XBitSet();
      while (isFeasible(hFilled, lb)) {
        int i = randomSetBit(XBitSet.all(fillable.length).subtract(xf));
        filledEdges.add(fillable[i]);
        xf.set(i);
        int u = fillable[i].u;
        int v = fillable[i].v;
        
        gFilled.addEdge(u, v);
        hFilled.addEdge(minor.map[u], minor.map[v]);
      }
      filled = new Edge[filledEdges.size()];
      filledEdges.toArray(filled);
      nf = filled.length;
      gFilled1 = g.copy();
      for (int i = 0; i < nf - 1; i++) {
        gFilled1.addEdge(filled[i].u, filled[i].v);
      }
    }
    
    
    boolean clearedBy(Contractor cont) {
      Minor minor = cont.contract(gFilled);
      return !isFeasible(minor.h, lb);
    }

    void shrinkFor(Contractor cont) {
      while (nf > 1 && !isTightFor(cont)) {
        nf--;
        gFilled.removeEdge(filled[nf].u, filled[nf].v);
        gFilled1.removeEdge(filled[nf - 1].u, filled[nf - 1].v);
      }
    }

    boolean isTightFor(Contractor cont) {
      Minor minor = cont.contract(gFilled1);
      return isFeasible(minor.h, lb);
    }

    int score(Contractor cont) {
      Minor minor = cont.contract(gFilled1);
      return nSSOf(minor.getGraph(), lb);
    }
    
    int nSSOf(Graph h, int lb) {
      SemiPIDFull spidfull = new SemiPIDFull(h, lb);
      spidfull.computeSafeSeps();
      return spidfull.safeSeps.size();      
    }
    
    public String toString() {
      return nf + " " + Arrays.deepToString(filled);
    }
  }
  
  public static void main(String args[]) {
    if (args.length == 3) {
      test(args[0], args[1], Integer.parseInt(args[2]));
      return;
    }

    // test("random", "gnm_070_210_1", 22);
    // test("random", "gnm_070_280_1");

    // test("random", "gnm_080_240_1");
    // test("random", "gnm_080_320_1");
    // test("random", "gnm_090_270_1");
    // test("random", "gnm_090_360_1");
    // test("random", "gnm_090_450_1");
    // test("instance/pace17exact", "ex001");
    // test("pace17exact", "ex002", 49);
    // test("pace17exact", "ex003", 44);
    // test("pace17exact", "ex004", 486);
    // test("pace17exact", "ex006", 7);
    // test("instance/pace17exact", "ex007");
    // test("pace17exact", "ex010", 9);
    // test("pace17exact", "ex014", 18);
    // test("pace17exact", "ex015", 15);
    // test("instance/pace17exact", "ex015");
    // test("pace17exact", "ex019", 11);
    // test("instance/pace17exact", "ex019");
    // test("pace17exact", "ex036", 119);
    // tst("pace17exact", "ex038", 26);
    // test("pace17exact", "ex041", 9);
    // test("pace17exact", "ex048", 15);
    // test("pace17exact", "ex049", 13);

    // test("pace17exact", "ex050", 28);
    // test("pace17exact", "ex052", 9);

    // test("pace17exact", "ex053", 9);
    // test("pace17exact", "ex057", 117);
    // test("pace17exact", "ex059", 10);
    // test("instance/pace17exact", "ex059");

    // test("pace17exact", "ex061", 22);
    // test("pace17exact", "ex063", 44);
    // test("pace17exact", "ex064", 7);
    // test("pace17exact", "ex065", 25);
    // test("pace17exact", "ex066", 15);
    // test("pace17exact", "ex075", 8);
    // test("pace17exact", "ex081", 6);
    // test("pace17exact", "ex091", 9);
    // test("pace17exact", "ex095", 11);
    // test("pace17exact", "ex096", 9);
    // test("pace17exact", "ex100", 12);
    // test("pace17exact", "ex107", 12);
    // test("pace17exact", "ex121", 34);
    // test("pace17exact", "ex162", 9);
//     test("instance/pace17exact", "ex006");
//    test("../instance/PACE2017bonus_gr/", "mrpp_4x4#8_8.gaifman_3", 24);
    
//    
//     test("../instance/PACE2017bonus_gr/", "Promedas_44_11", 18);
//    test("../instance/PACE2017bonus_gr/", "Promedas_58_11", 24);
    // test("instance/Promedas/", "Promedas_58_11");
    // test("instance/Promedas/", "Promedas_68_13");
    // test("instance/Promedas/)", "Promedas_51_14");
//     test("../instance/PACE2017bonus_gr/", "Promedas_62_11", 21);
    // test("instance/test/", "Promedas_46_15_145");
//    test("../instance/PACE2017bonus_gr/",
//    "jgiraldezlevy.2200.9086.08.40.93.gaifman_2", 36);
//    test("../instance/PACE2017bonus_gr/",
//    "jgiraldezlevy.2200.9086.08.40.41.gaifman_2", 34);
//    test("../instance/PACE2017bonus_gr/",
//        "modgen-n200-m90860q08c40-22556.gaifman_2", 36);
//    test("../instance/PACE2017bonus_gr/",
//        "modgen-n200-m90860q08c40-14808.gaifman_2", 35);
    // test("../instance/PACE2017bonus_gr/", "Promedus_34_14", 36);
//    test("../instance/PACE2017bonus_gr/", "Promedas_24_11", 12);
    // test("instance/Promedas/", "Promedus_18_10", 14);
    // test("instance/Promedas/", "Promedas_55_9", 13);
//     test("../instance/PACE2017bonus_gr/", "Promedus_27_15", 13);
//     test("../instance/PACE2017bonus_gr/", "Promedas_51_12", 13);
//    test("../instance/PACE2017bonus_gr/", "Promedus_17_13", 13);
//    test("../instance/PACE2017bonus_gr/", "Promedus_11_15", 13);
//    test("../instance/PACE2017bonus_gr/", "Promedus_14_8", 14);
//    test("../instance/PACE2017bonus_gr/", "Promedus_28_14", 11);
    // test("instance/Promedas/", "Promedas_46_15", 13);
    // test("instance/PACE2017bonus_gr/", "Pedigree_13_9", 16);
    // test("instance/PACE2017bonus_gr/", "Pedigree_12_12", 16);
    // test("instance/Promedas/", "Promedas_55_9", 13);
//     test("../instance/PACE2017bonus_gr/", "mrpp_8x8#24_14.gaifman_3", 28);
    // test("instance/PACE2017bonus_gr/", "NY_11", 10);
    // test("instance/PACE2017bonus_gr/", "am_9_9.gaifman_6", 15);
//    test("../instance/PACE2017bonus_gr/", "Promedus_14_8", 14);
//     test("../instance/PACE2017bonus_gr/", "Promedus_11_15", 13);
//     test("../instance/PACE2017bonus_gr/", "Promedus_17_13", 13);
    //
    // test("instance/Promedas/", "Promedas_62_9", 13);
    //
    // test("instance/Promedas/", "Promedas_34_8", 14);
    // test("instance/Promedas/", "Promedus_18_10", 14);
//     test("../instance/PACE2017bonus_gr/", "NY_13", 9);
    // test("instance/Promedas/", "Promedas_32_8", 13);
    // test("instance/Promedas/", "Promedas_44_9", 12);
    // test("instance/Promedas/", "Promedus_12_14", 11);
    // test("instance/Promedas/", "Promedus_12_15", 11);
    // test("instance/PACE2017bonus_gr/", "Pedigree_12_14", 15);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_11", 14);
    // test("instance/Promedas/", "Promedas_63_8", 14);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_12", 14);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_13", 14);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_15", 14);
    // test("instance/PACE2017bonus_gr/", "FLA_15", 9);
    // test("instance/Promedas/", "Promedas_22_8", 13);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_10", 14);
    // test("instance/PACE2017bonus_gr/", "Pedigree_13_12", 15);
    // test("instance/Promedas/", "Promedus_20_13", 12);
    // test("instance/Promedas/", "Promedas_11_7", 13);
    // test("instance/PACE2017bonus_gr/",
    // "smtlib-qfbv-aigs-lfsr_004_127_112-tseitin.gaifman_6", 13);
    // test("instance/Promedas/", "Promedas_28_10", 11);
    // test("instance/PACE2017bonus_gr/", "SAT_dat.k80-24_1_rule_1.gaifman_3", 22);
    // test("instance/PACE2017bonus_gr/", "LKS_13", 9);
    // test("instance/PACE2017bonus_gr/", "am_7_7.shuffled-as.sat03-363.gaifman_6",
    // 9);
    // test("instance/PACE2017bonus_gr/", "FLA_13", 9);
    // test("instance/Promedas/", "Promedas_30_7", 13);
    // test("instance/Promedas/", "Promedas_61_8", 13);
    // test("instance/PACE2017bonus_gr/",
    // "jgiraldezlevy.2200.9086.08.40.93.gaifman_2", 36);
    // test("instance/PACE2017bonus_gr/",
    // "modgen-n200-m90860q08c40-22556.gaifman_2", 33);
    // test("instance/Promedas/", "Promedas_34_14", 12);
    // test("instance/PACE2017bonus_gr/",
    // "jgiraldezlevy.2200.9086.08.40.167.gaifman_2", 34);
    // test("instance/PACE2017bonus_gr/", "newton.3.3.i.smt2-stp212.gaifman_2", 19);
    // test("instance/Promedas/", "Promedas_69_10", 12);
    // test("instance/Promedas/", "Promedas_60_11", 11);
    // test("../instance/PACE2017bonus_gr/", "Promedas_59_10", 11);
    // test("instance/Promedas/", "Promedas_21_9", 11);
    // test("instance/Promedas/", "Promedus_28_14", 11);
    // test("instance/Promedas/", "Promedas_23_6", 12);
    // test("instance/PACE2017bonus_gr/", "LKS_15", 10);
    // test("instance/PACE2017bonus_gr/", "6s151.gaifman_3", 14);
    // test("instance/Promedas/", "Promedus_18_8", 13);
//     test("../instance/PACE2017bonus_gr/", "aes_24_4_keyfind_5.gaifman_3", 23);
    // test("instance/Promedas/", "Promedas_22_6", 12);
    // test("instance/Promedas/", "Promedus_34_12", 11);
    // test("instance/PACE2017bonus_gr/", "Pedigree_12_8", 14);
    // test("instance/Promedas/", "Promedas_25_8", 11);
    // test("instance/PACE2017bonus_gr/",
    // "jgiraldezlevy.2200.9086.08.40.22.gaifman_2", 33);
    // test("instance/PACE2017bonus_gr/",
    // "jgiraldezlevy.2200.9086.08.40.46.gaifman_2", 33);
    // test("instance/Promedas/", "Promedas_45_7", 12);
    // test("instance/Promedas/", "Promedas_27_8", 12);
    // test("instance/PACE2017bonus_gr/", "Pedigree_11_6", 14);
//    test("../instance/PACE2017bonus_gr/", 
//        "aes_24_4_keyfind_5.gaifman_3", 23);
//    test("../instance/PACE2017bonus_gr/", "Promedus_38_14", 10);
    test("../instance/PACE2017bonus_gr/", "Promedus_38_15", 10);
    // test("instance/PACE2017bonus_gr/",
    // "modgen-n200-m90860q08c40-14808.gaifman_2", 35);
    // test("instance/PACE2017bonus_gr/",
    // "jgiraldezlevy.2200.9086.08.40.41.gaifman_2", 34);
    // test("instance/Promedas/", "Promedus_14_9", 12);
    // test("instance/Promedas/", "Promedas_46_8", 11);
    // test("instance/Promedas/", "Promedas_43_13", 10);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro_14", 13);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro_15", 13);
    // test("instance/Promedas/", "Promedus_34_11", 11);
    // test("instance/Promedas/", "Promedas_50_7", 12);
    // test("instance/Promedas/", "Promedus_38_15", 10);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro+tram_9", 13);
    // test("instance/PACE2017bonus_gr/", "mrpp_4x4#8_8.gaifman_3", 24);
    // test("instance/PACE2017bonus_gr/", "countbitsarray04_32.gaifman_10", 13);
    // test("instance/PACE2017bonus_gr/", "Pedigree_11_7", 14);
    // test("instance/PACE2017bonus_gr/", "post-cbmc-aes-d-r2", 11);
    // test("instance/PACE2017bonus_gr/", "FLA_14", 8);
    // test("instance/Promedas/", "Promedas_49_8", 10);
    // test("instance/PACE2017bonus_gr/", "minxor128.gaifman_2", 4);
    // test("instance/Promedas/", "Promedas_48_5", 11);
    // test("../instance/PACE2017bonus_gr/", "Promedas_56_8", 10);
    // test("instance/Promedas/", "Promedas_56_8", 10);
    // test("instance/PACE2017bonus_gr/",
    // "GTFS_VBB_EndeApr_Dez2016.zip_train+metro_12", 11);
    // test("../instance/PACE2017bonus_gr/", "Promedas_69_9", 9);
    // test("instance/Promedas/", "", 9);
    // test("instance/PACE2017bonus_gr/", "MD5-32-1.gaifman_4", 12);
    // test("instance/PACE2017bonus_gr/", "Sz512_15127_1.smt2-stp212.gaifman_3",
    // 14);
  }
  
  void updateBests(int k, Contractor cont) {
    bestContractor[k] = cont;
    while (k > g.n - BASE_SIZE && 
        (bestContractor[k - 1] == null || cont.compareTo(bestContractor[k - 1]) < 0)) { 
      bestContractor[k--] = cont;
    }
  }

  private static void test(String path, String name, int upperBound) {
    log = new Log("Multifilter" + VERSION + "_" + BASE_SIZE + "_" + UNC_CHUNK + "_" + N_TRY, 
        name);

    Graph g = Graph.readGraph(path, name);
    // Graph g = Graph.readGraph("instance/" + path, name);

    log.log("Graph " + name + " read, n = " + g.n + ", m = " + g.numberOfEdges());

    t0 = System.currentTimeMillis();
        
    ACSDecomposition acsd = new ACSDecomposition(g);
    acsd.decomposeByACS();
    XBitSet largestAtom = null;
    for (XBitSet atom : acsd.acAtoms) {
      if (largestAtom == null || atom.cardinality() > largestAtom.cardinality()) {
        largestAtom = atom;
      }
    }

    log.log("Largest atom: " + largestAtom.cardinality());

    LocalGraph local = new LocalGraph(g, largestAtom);

    MultiFilter mf = new MultiFilter(local.h);
    int lb = mf.initialLowerBound();
    log.log("initial lower bound " + lb + ", " + (System.currentTimeMillis()- t0) + " milliseds");
    while (lb < upperBound) {
      lb = mf.improvedLowerBound();
      log.log("improved lower bound " + lb  + ", " + (System.currentTimeMillis()- t0) + " milliseds");
    }
    log.log("lower bound = " + lb + ", " + (System.currentTimeMillis()- t0) + " milliseds");
  }


}
