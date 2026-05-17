package tw.lb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
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
import tw.common.Subgraph;
import tw.common.TreeDecomposition;
import tw.decomposer.SemiPID;
import tw.decomposer.SemiPIDFull;
import tw.acsd.ACSDecomposition;

public class SepDestruction1 {
  static final boolean VERBOSE = true;
//  static final boolean VERBOSE = false;
  static final boolean TRACE = true;
//  static final boolean TRACE = false;
//  static final boolean VERIFY = true;

  static final int BASE_SIZE = 70;
  static final String VERSION = "1";

  Graph g;
  public int lb;
  public Minor obs;
  
  Edge[] contracted;
  XBitSet allCont;
  
  Random random;

  static long t0;
  

  static Log log;

  public SepDestruction1(Graph g) {
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
    Graph h = obs.getGraph();
    if (h.isClique(h.all)) {
      return improveClique(obs);
    }
    
    contracted = obs.contractionEdges();
    
    allCont = XBitSet.all(contracted.length);
    
    XBitSet current = allCont; 
    while (!clears(current, g)) {
      if (TRACE) {
        System.out.println("current: graph size " + (g.n - current.cardinality()) + 
            " uncont " + allCont.subtract(current));
      }

      XBitSet targetSep = sepToDestroy(current);
      
      XBitSet cont = destroy(targetSep, current);
      current = cont;
    }
    
    return deriveObstruction(contract(g, current));
  }


  XBitSet alternativelyImprove(XBitSet current) {
    return null;
  }

  XBitSet destroy(XBitSet targetSep, XBitSet cont) {
    if (TRACE) {
      System.out.println("destroying " + targetSep);
    }

    Minor minor = contract(g, cont);
    XBitSet uncont = new XBitSet();
    for (int i = cont.nextSetBit(0); i >= 0; i = cont.nextSetBit(i + 1)) {
      Edge e = contracted[i];
      if (minor.map[e.u] == minor.map[e.v] &&
          targetSep.get(minor.map[e.u])) {
        uncont.set(i);
      }
    }
    
    XBitSet sepExpanded = expansion(targetSep, minor);
    if (TRACE) {
      System.out.println("expanded " + sepExpanded);
    }

    LocalGraph lg = new LocalGraph(g, sepExpanded);
    if (isFeasible(lg.h, lb)) {
      if (TRACE) {
        System.out.println("local graph feasible");
      }
      return cont.subtract(uncont);
    }

    if (TRACE) {
      System.out.println("local graph infeasible");
    }
    
    Graph gs = lg.h;
    Minor sMinor = new Minor(gs);
    boolean moving = true;
    XBitSet rem = (XBitSet) uncont.clone();
    while (moving) {
      if (TRACE) {
        System.out.println("uncont " + uncont);
        System.out.println("rem " + rem);
      }
      moving = false;
      for (int i = rem.nextSetBit(0); i >= 0; i = rem.nextSetBit(i + 1)) {
        rem.clear(i);
        Edge e = contracted[i];
        XBitSet uncont1 = uncont.removeBit(i);
        Minor sMinor1 = sMinor.contract(
            sMinor.map[lg.conv[e.u]], sMinor.map[lg.conv[e.v]]);
        if (!isFeasible(sMinor1.getGraph(), lb)) {
          moving = true;
          uncont = uncont1;
          sMinor = sMinor1;
          break;
        }
      }
    }
    return cont.subtract(uncont);
  }

  private XBitSet sepToDestroy(XBitSet cont) {
    Minor minor = contract(g, cont);
    Graph h = minor.getGraph();
    SemiPIDFull spdf = new SemiPIDFull(h, lb);
    spdf.computeSafeSeps();
    Set<XBitSet> safeSeps = spdf.safeSeps;
    
    XBitSet best = null;
    int ncBest = 0;
    int xsBest = 0;
    for (XBitSet sep: safeSeps) {
      int xs = expansion(sep, minor).cardinality();
      int nc = nCross(sep, h, safeSeps);
      if (best == null) {
        best = sep;
        xsBest = xs;
        ncBest = nc;
      }
      else if (xsBest > BASE_SIZE && xs < xsBest) {
        best = sep;
        xsBest = xs;
        ncBest = nc;
      }
      else if (xs <= BASE_SIZE && nc < ncBest) {
        best = sep;
        xsBest = xs;
        ncBest = nc;
      }
    }
    return best;
  }

  int nCross(XBitSet sep, Graph h, Set<XBitSet> safeSeps) {
    int count = 0;
    ArrayList<XBitSet> components = h.separatedComponents(sep);
    for (XBitSet sep1: safeSeps) {
      if (crosses(sep1, components)) {
        count++;
      }
    }
    return count;
  }

  boolean crosses(XBitSet sep, ArrayList<XBitSet> components) {
    int count = 0;
    for (XBitSet compo: components) {
      if (sep.intersects(compo)) {
        count++;
      }
    }
    return count >= 2;
  }

  XBitSet expansion(XBitSet sep, Minor minor) {
    XBitSet s = new XBitSet();
    for (int v = sep.nextSetBit(0); v >= 0; v = sep.nextSetBit(v + 1)) {
      s.or(minor.components[v]);
    }
    return s;
  }

  boolean clears(XBitSet current, Graph h) {
    Minor minor = contract(h, current);
    return !isFeasible(minor.getGraph(), lb);
  }

  Minor contract(Graph h, XBitSet cont) {
    Minor minor = new Minor(h);
    for (int i = cont.nextSetBit(0); i >= 0; i = cont.nextSetBit(i + 1)) {
      Edge e = contracted[i];
      minor = minor.contract(minor.map[e.u], minor.map[e.v]);
    }
    return minor;
  }

  private Minor improveClique(Minor obs2) {
    // TODO Auto-generated method stub
    return null;
  }

  int bestToFreeze(Graph gFrozen, Minor minor) {
    Graph h = minor.getGraph();
    if (TRACE) {
      System.out.println("h.n " + h.n + " h.m " + h.numberOfEdges());
      h.printRaw(System.out);
    }
    ACPPID acp = new ACPPID(h, lb);
    acp.generateFeasibles();
    
    if (TRACE) {
      System.out.println(acp.feasibles.size() + " feasibles");
      for (XBitSet c: acp.feasibles) {
        System.out.println(" " + c);
      }
    }
    Set<XBitSet> stronglyFeasibles = new HashSet<>();
    for (XBitSet compo: acp.feasibles) {
      if (isStronglyFeasible(compo, h, acp.feasibles)) {
        stronglyFeasibles.add(compo);
      }
    }
    if (TRACE) {
      System.out.println(stronglyFeasibles.size() + " strongly feasibles");
    }
    
    int best = -1;
    
    for (int v = 0; v < h.n; v++) {
      if (minor.components[v].cardinality() == 1) {
        continue;
      }
      if (freezable(v, stronglyFeasibles, gFrozen, minor) &&
          (best == -1 || 
          minor.components[v].cardinality() > minor.components[best].cardinality())) {
        best = v;
      }
    }
    
    return best;
  }

  boolean freezable(int v, Set<XBitSet> stronglyFeasibles, Graph g, Minor minor) {
    Graph h = minor.getGraph();
    for (XBitSet compo: stronglyFeasibles) {
//      if (TRACE) {
//        System.out.println(compo + " " + compo.get(v));
//      }
      if (compo.get(v) && decomposableAt(v, compo, h, stronglyFeasibles)) {
//        if (TRACE) {
//          System.out.println("testing " + compo);
//        }
        XBitSet vs = h.closedNeighborSet(compo);
        XBitSet sep = vs.subtract(compo);
        XBitSet vsg = new XBitSet();
        XBitSet cg = new XBitSet();
        for (int w = vs.nextSetBit(0); w >= 0; w = vs.nextSetBit(w + 1)) {
          vsg.or(minor.components[w]);
          if (compo.get(w)) {
            cg.or(minor.components[w]);
          }
        }
        
        if (sep.cardinality() + cg.cardinality() > BASE_SIZE) {
          return false;
        }
        
        Subgraph sub = new Subgraph(g, vsg);
        
        XBitSet[] compos = new XBitSet[sep.cardinality() + cg.cardinality()];

        int[] sa = sep.toArray();
        for (int i = 0; i < sa.length; i++) {
          compos[i] = minor.components[sa[i]].convert(sub.conv);
        }
        
        int[] ca = cg.toArray();
        assert compos.length == sa.length + ca.length; 
        for (int i = 0; i < ca.length; i++) {
          compos[i + sa.length] = new XBitSet(new int[] {sub.conv[ca[i]]});  
        }
        
        Minor minor1 = new Minor(sub.h, compos);
        
        Graph h1 = minor1.getGraph();
        h1.fill(XBitSet.all(sa.length));

        if (!isFeasible(minor1.getGraph(), lb)) {
          return false; 
        }
      }
    }
    return true;
  }

  boolean decomposableAt(int v, XBitSet compo, Graph h, Set<XBitSet> stronglyFeasibles) {
    ArrayList<XBitSet> components = h.componentsOf(compo.removeBit(v));
    for (XBitSet c: components) {
      if (!stronglyFeasibles.contains(c)) {
        if (TRACE) {
          System.out.println("for " + v + " not decomposabele " + compo);
        }
        return false;
      }
    }
    if (TRACE) {
      System.out.println("for " + v + " decomposabele " + compo);
    }
    return true;
  }

  boolean isStronglyFeasible(XBitSet compo, Graph h, Set<XBitSet> feasibles) {
    ArrayList<XBitSet> components = h.separatedComponents(h.closedNeighborSet(compo));
    for (XBitSet c: components) {
      if (!feasibles.contains(c)) {
        return false;
      }
    }
    return true;
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

  private static void test(String path, String name, int upperBound) {
    log = new Log("SepDestruction" + VERSION, name);

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

    SepDestruction1 mf = new SepDestruction1(local.h);
    int lb = mf.initialLowerBound();
    log.log("initial lower bound " + lb + ", " + (System.currentTimeMillis()- t0) + " milliseds");
    while (lb < upperBound) {
      lb = mf.improvedLowerBound();
      log.log("improved lower bound " + lb  + ", " + (System.currentTimeMillis()- t0) + " milliseds");
    }
    log.log("lower bound = " + lb + ", " + (System.currentTimeMillis()- t0) + " milliseds");
  }


}
