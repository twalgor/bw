package tw.minseps;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

import tw.common.Edge;
import tw.common.Graph;
import tw.common.Minor;
import tw.common.XBitSet;

public class FragileMinSeps1 {
//  static final boolean TRACE = true;
  static boolean TRACE = false;
  Graph g;
  Edge e;
  int k;
  
  public Set<XBitSet> minSeps;
  
  public FragileMinSeps1(Graph g, Edge e, int k) {
    this.g = g;
    this.e = e;
    this.k = k;
//    TRACE = g.n <= 11;
    if (TRACE) {
      System.out.println("FragileMinSeps n = " + g.n + 
          ", e = " + e);
    }
  }
  
  public void generate() {
    minSeps = new HashSet<>();
    generate(e.u, e.v);
    generate(e.v, e.u);
  }
  
  void generate(int a, int s) {
    assert g.neighborSet[a].get(s);
    XBitSet aNeighb = g.neighborSet[a];
    XBitSet bs = g.neighborSet[s].removeBit(a);
    XBitSet sFixed = new XBitSet(new int[] {s}); 
    generateFrom(a, 
        new XBitSet(new int[] {a}), 
        bs,
        aNeighb,
        sFixed,
        aNeighb.removeBit(s),
        "");
  }
  
  void generateFrom(int a, 
      XBitSet aSide, 
      XBitSet bTargets, 
      XBitSet separator,
      XBitSet sFixed,
      XBitSet aNeighbUndecided,
      String indent) {

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
        branch(a, aSide, full, bTargets, separator, sFixed, aNeighbUndecided, indent);
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
          branch(a, c, bCompo, bTargets, sep, sFixed, 
              aNeighbUndecided.intersectWith(sep), indent);
          break;
        }
      }
    }
  }
  
  boolean neverFragile(XBitSet aSide, int a, XBitSet separator) {
    XBitSet aSide1 = aSide.removeBit(a);
    if (g.isConnected(aSide1) &&
        g.neighborSet[a].intersectWith(separator).isSubset(g.neighborSet(aSide1))) {
      return true;
    }
    return false;
  }

  void branch(int a, XBitSet aSide, XBitSet bSide, XBitSet bTargets, XBitSet separator, 
      XBitSet sFixed, XBitSet aNeighbUndecided,       
      String indent) {
    if (TRACE) {
      System.out.println(indent + "branch for a = " + a + 
          ", aSide = " + aSide);
      System.out.println(indent + "bSide = " + bSide);
      System.out.println(indent + "separator = " + separator);
      System.out.println(indent + "sFixed = " + sFixed);
      System.out.println(indent + "aNeighbUndecided = " + aNeighbUndecided);

      System.out.println(indent + minSeps.size() + " minSeps so far");
    }

    assert sFixed.isSubset(separator);
    assert sFixed.cardinality() <= k;
    assert g.neighborSet(aSide).equals(separator);
    assert g.neighborSet(bSide).equals(separator);
    assert aNeighbUndecided.isSubset(separator);
    assert !aNeighbUndecided.intersects(sFixed);

    if (aNeighbUndecided.isEmpty()) {
      if (neverFragile(aSide, a, separator)) {
        return;
      }
    }
    
    if (TRACE) {
      System.out.println(indent + "sFixed " + sFixed);
    }

    if (sFixed.equals(separator)) {
      assert aNeighbUndecided.isEmpty();
      assert !neverFragile(aSide, a, separator);
      if (isFragile(separator)) {
        if (TRACE) {
          System.out.println(indent + "minSep added: " + separator);
        }
        minSeps.add(separator);
      }
      return;
    }
    
    int u = aNeighbUndecided.nextSetBit(0);
    if (u >= 0) {
      generateFrom(a, aSide.addBit(u), bTargets, 
        separator.removeBit(u).unionWith(g.neighborSet[u].subtract(aSide)),
        sFixed, 
        aNeighbUndecided.removeBit(u), 
        indent + " ");
      if (sFixed.cardinality() < k) {
        generateFrom(a, aSide, bTargets, 
            separator,
            sFixed.addBit(u), 
            aNeighbUndecided.removeBit(u), 
            indent + " ");
      }
      return;
    }
    XBitSet toDecide = separator.subtract(sFixed);
    
    if (TRACE) {
      System.out.println(indent + "toDecide " + toDecide);
    }

    if (toDecide.isEmpty()) {
      return;
    }

    
    int v = largestNeighborhoodVertex(toDecide, bSide);
    if (TRACE) {
      System.out.println(indent + "branching on " + v);
    }
//    XBitSet rest = bSide.subtract(g.neighborSet[v]);
    XBitSet nb = g.neighborSet[v].subtract(separator);
    nb.andNot(aSide);
    XBitSet separator1 = separator.removeBit(v).unionWith(nb);
    generateFrom(a, aSide.addBit(v), bTargets, 
      separator1, sFixed, aNeighbUndecided, indent + " ");

    if (sFixed.cardinality() < k) {
      branch(a, aSide, bSide, bTargets, separator, sFixed.addBit(v),
          aNeighbUndecided, indent + " ");
    }
  }
  
  boolean isFragile(XBitSet minSep) {
    Minor minor = new Minor(g);
    minor = minor.contract(e.u, e.v);
    return minor.h.fullComponents(minSep.convert(minor.map)).size() < 2;
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

