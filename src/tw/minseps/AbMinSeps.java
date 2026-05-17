package tw.minseps;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

import tw.common.Graph;
import tw.common.XBitSet;

public class AbMinSeps {
//  static final boolean TRACE = true;
  static boolean TRACE = false;
  Graph g;
  XBitSet sa;
  int b;
  int k;
  XBitSet aExcluded;
  public Set<XBitSet> minSeps;
  
  public AbMinSeps(Graph g, XBitSet sa, int b, int k) {
    this.g = g;
    this.k = k;
    this.sa = sa;
    this.b = b;
//    TRACE = g.n <= 11;
    if (TRACE) {
      System.out.println("AbMinSeps n = " + g.n + 
          ", sa = " + sa + " b = " + b + ", k = " + k);
    }
  }
  
  public void generate() {
    minSeps = new HashSet<>();
    Integer[] vertices = new Integer[g.n];
    for (int i = 0; i < g.n; i++) {
      vertices[i] = i;
    }

    Arrays.sort(vertices, new NeighborSizeComparator());

    generateFrom(b, new XBitSet(new int[] {b}), sa, 
        g.neighborSet[b], new XBitSet(), new XBitSet(), "");
    
    aExcluded = new XBitSet(g.n);
    for (int a : sa.toArray()) {
      XBitSet aSide = new XBitSet(new int[] {a});
      XBitSet bSide = new XBitSet(new int[] {b});
      XBitSet sFixed = g.neighborSet[a].intersectWith(aExcluded);
      if (sFixed.cardinality() > k) {
        continue;
      }
      generateFrom(a, aSide, bSide, g.neighborSet[a],  
          sFixed, aExcluded, "");
      aExcluded.set(a);
    }
  }

  void generateFrom(int a, XBitSet aSide, XBitSet bTargets, XBitSet separator, XBitSet sFixed,
      XBitSet aExcluded, String indent) {

    assert g.neighborSet(aSide).equals(separator);
    ArrayList<XBitSet> fulls = new ArrayList<>();
    ArrayList<XBitSet> nonFulls = new ArrayList<>();
    XBitSet rest = g.all.subtract(aSide).subtract(separator);
    g.listComponents(rest, separator, fulls, nonFulls);
    
    for (XBitSet full: fulls) {
      if (TRACE) {
        System.out.println(indent + "full" + full);
      }
      if (full.intersects(bTargets)) {
        branch(a, aSide, full, bTargets, separator, sFixed, aExcluded, indent);
      }
    }
    
    for (XBitSet bCompo: nonFulls) {
      if (!bTargets.intersects(bCompo)) {
        continue;
      }
      XBitSet sep = g.neighborSet(bCompo);
      if (!sFixed.isSubset(sep)) {
        continue;
      }
      XBitSet rest1 = g.all.subtract(bCompo);
      rest1.andNot(sep);
      ArrayList<XBitSet> compos = g.componentsOf(rest1);
      for (XBitSet c: compos) {
        if (c.get(a)) {
          if (!c.intersects(aExcluded)) {
            branch(a, c, bCompo, bTargets, sep, sFixed, aExcluded, indent);
          }
          break;
        }
      }
    }
  }
  
  void branch(int a, XBitSet aSide, XBitSet bSide, XBitSet bTargets, XBitSet separator, 
      XBitSet sFixed, XBitSet aExcluded,       
      String indent) {
    if (TRACE) {
      System.out.println(indent + "branch for a = " + a + 
          ", aSide = " + aSide);
      System.out.println(indent + "bSide = " + bSide);
      System.out.println(indent + "separator = " + separator);
      System.out.println(indent + "sFixed = " + sFixed);

      System.out.println(indent + minSeps.size() + " minSeps so far");
    }

    int nA = aSide.cardinality();
    int nS = separator.cardinality();
    if (nS <= k && nA > (g.n - nS) / 2
      || nS > k && nA + (nS - k) > (g.n - k) / 2) {
      return;
    }

    assert sFixed.isSubset(separator);
    assert sFixed.cardinality() <= k;
    assert g.neighborSet(aSide).equals(separator);
    assert g.neighborSet(bSide).equals(separator);
    if (separator.cardinality() <= k) {
      if (TRACE) {
        System.out.println(indent + "minSep added: " + separator);
      }
      minSeps.add(separator);
    }
    if (TRACE) {
      System.out.println(indent + "sFixed " + sFixed);
    }

    if (sFixed.cardinality() == k) {
      return;
    }
    
    XBitSet toDecide = separator.subtract(sFixed);
    assert !toDecide.intersects(aExcluded);
    
    if (TRACE) {
      System.out.println(indent + "toDecide " + toDecide);
    }

    if (toDecide.isEmpty()) {
      return;
    }
    
    
//    if (sterile(aSide, bSide, separator, sFixed)) {
//      return;    
//    }
    
    int v = largestNeighborhoodVertex(toDecide, bSide);
    if (TRACE) {
      System.out.println(indent + "branching on " + v);
    }
//    XBitSet rest = bSide.subtract(g.neighborSet[v]);
    XBitSet nb = g.neighborSet[v].subtract(separator);
    nb.andNot(aSide);
    XBitSet separator1 = separator.removeBit(v).unionWith(nb);
    XBitSet sFixed1 = sFixed.unionWith(nb.intersectWith(aExcluded));
    if (TRACE) {
      System.out.println(indent + "sFixed1 = " + sFixed1);
    }
    if (sFixed1.cardinality() <= k) {
      generateFrom(a, aSide.addBit(v), bTargets, 
        separator1, sFixed1, aExcluded, indent + " ");
    }
    if (sFixed.cardinality() < k) {
      branch(a, aSide, bSide, bTargets, separator, sFixed.addBit(v), aExcluded, indent + " ");
    }
  }
  
  int largestNeighborhoodVertex(XBitSet toDecide, XBitSet bSide) {
    int vLargest = toDecide.nextSetBit(0);
    assert vLargest >= 0;
    int sLargest = g.neighborSet[vLargest].intersectWith(bSide).cardinality();
    for (int v = toDecide.nextSetBit(vLargest); v >= 0; v = toDecide.nextSetBit(v + 1)) {
      int sN = g.neighborSet[v].intersectWith(bSide).cardinality(); 
      if (sN > sLargest) {
        vLargest = v;
        sLargest = sN;
      }
    }
    return vLargest;
  }

  boolean sterile(XBitSet aSide, XBitSet bSide, XBitSet separator, XBitSet sFixed) {
    int nA = aSide.cardinality();
    int nB = bSide.cardinality();
    int nS = separator.cardinality();
    int nF = sFixed.cardinality();
    int nR = nS - nF;
    assert nR > 0;

    XBitSet toDecide = separator.subtract(sFixed);
        
    if (nS > k) {
      if (nA + (nS - k) > (g.n - k) / 2) {
        return true;
      }
      // nA + nS + want - k > (g.n - k) / invAlpha
      int want = (g.n - k) / 2 - nA - nS + k + 1;
      
      if (want * (nS - nF) > nB * (nS - k)) {
        return false;
      }

//      if (true) {
//        return false;
//      }
      // sterility check with vertex disjoint paths(with hanging trees)
      XBitSet rest = (XBitSet) bSide.clone();
      XBitSet[] treeNeighbors = new XBitSet[nR];

      {
        int i = 0;
        for (int v = toDecide.nextSetBit(0);
            v >= 0; v = toDecide.nextSetBit(v + 1)) {
          treeNeighbors[i++] =
              g.neighborSet[v].intersectWith(rest);
        }
      }
      int taken = 0;
      int nSurviving = nR;
      int depth = 0;
      assert k > nF;
      while (true) {
        for (int i = 0; i < nSurviving; i++) {
          treeNeighbors[i].and(rest);
        }
        Arrays.sort(treeNeighbors, 0, nSurviving, 
            XBitSet.cardinalityComparator);
        if (taken - depth * (k - nF) +  
            treeNeighbors[nSurviving - (k - nF) - 1].cardinality()
            >= want) { 
          return true;
        }
        int j = 0;
        for (int i = 0; i < nSurviving; i++) {
          treeNeighbors[i].and(rest);
          if (!treeNeighbors[i].isEmpty()) {
            int w = treeNeighbors[i].nextSetBit(0);
            treeNeighbors[i].clear(w);
            taken++;
            treeNeighbors[i].or(g.neighborSet[w].intersectWith(rest));
            rest.clear(w);
            treeNeighbors[j++] = treeNeighbors[i];
          }
        }
        nSurviving = j;
        depth++;

        if (nSurviving < (k - nF)) {
          break;
        }
        if (taken - (k - nF) * depth >= want) {
          return true;
        }
        if (nSurviving == k - nF) {
          break;
        }
      }
    }
    return false;
  }

  class NeighborSizeComparator implements Comparator<Integer> {
    @Override
    public int compare(Integer v, Integer w) {
      int c = g.neighborSet[w].cardinality() - 
          g.neighborSet[v].cardinality();
      if (c != 0) return c;
      return v - w;
    }
  }
}

