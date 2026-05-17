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

public class FragileMinSeps {
  static final boolean TRACE = true;
//  static boolean TRACE = false;
  Graph g;
  Edge e;
  int k;
  
  int a;
  XBitSet aNeighbors;
  XBitSet bTargets;
  
  public Set<XBitSet> minSeps;
  
  public FragileMinSeps(Graph g, Edge e, int k) {
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
    this.a = a;
    aNeighbors = g.neighborSet[a];
    assert aNeighbors.get(s);
    bTargets = g.neighborSet[s].removeBit(a);
    generateFrom(
        new XBitSet(), // aMain
        new XBitSet().addBit(a), // aSide
        aNeighbors, // separator
        new XBitSet(), // aMainNb
        new XBitSet(new int[] {s}), // sFixed
        "");
  }
  
  void generateFrom(
      XBitSet aMain, 
      XBitSet aSide, 
      XBitSet separator,
      XBitSet aMainNb, 
      XBitSet sFixed,
      String indent) {

    assert aSide.get(a);
    assert separator.equals(g.neighborSet(aSide));
    assert aMain.isSubset(aSide.removeBit(a));
    assert g.isConnected(aMain);
    assert aMainNb.equals(g.neighborSet(aMain).removeBit(a)):
      aMainNb + " " + g.neighborSet(aMain);
    assert aMainNb.isSubset(separator);


    ArrayList<XBitSet> fulls = new ArrayList<>();
    ArrayList<XBitSet> nonFulls = new ArrayList<>();
    XBitSet rest = g.all.subtract(aSide).subtract(separator);
    g.listComponents(rest, separator, fulls, nonFulls);
    if (TRACE) {
      System.out.println(indent + "a " + a + " aMain " + aMain + 
          " aSide " +  aSide + " separator " + separator + 
          " aMainNb " + aMainNb + " " + fulls.size() + " fulls " + 
          nonFulls.size() + " non-fulls");
    }
    
    for (XBitSet full: fulls) {
      if (TRACE) {
        System.out.println(indent + "full" + full);
      }
      if (full.intersects(bTargets)) {
        
        branch(aMain, aSide, full, separator, aMainNb, sFixed, indent);
      }
    }
    
    for (XBitSet bCompo: nonFulls) {
      if (!bTargets.intersects(bCompo)) {
        if (TRACE) {
          System.out.println(indent + "bCompo " + bCompo + " does not intersect bTargets " + bTargets);
        }
        continue;
      }
      XBitSet sep = g.neighborSet(bCompo);
      if (TRACE) {
        System.out.println(indent + "bCompo " + bCompo + " sep " + sep);
      }
      if (!sFixed.isSubset(sep)) {
        continue;
      }
      XBitSet rest1 = g.all.subtract(bCompo);
      rest1.andNot(sep);
      ArrayList<XBitSet> compos = g.componentsOf(rest1);
      for (XBitSet c: compos) {
        if (c.get(a)) {
          ArrayList<XBitSet> compos1 = g.componentsOf(c.removeBit(a));
          XBitSet aMain1 = null;
          if (!aMain.isEmpty()) {
            for (XBitSet c1: compos1) {
              if (c1.intersects(aMain)) {
                aMain1 = c1;
                break;
              }
            }
            assert aMain1 != null;
          }
          else {
            aMain1 = compos1.get(0);
            XBitSet nb1 = g.neighborSet(aMain1);
            for (XBitSet c1: compos1) {
              if (g.neighborSet(c1).cardinality() > nb1.cardinality()) {
                aMain1 = c1;
                nb1 = g.neighborSet(c1);
              }
            }
          }
          branch(aMain1, c, bCompo, sep, g.neighborSet(aMain1).removeBit(a), sFixed, indent); 
          break;
        }
      }
    }
  }
  
  void branch(XBitSet aMain, XBitSet aSide, XBitSet bSide, XBitSet separator, 
      XBitSet aMainNb, XBitSet sFixed, String indent) {
    if (TRACE) {
      System.out.println(indent + "branch for a = " + a + 
          ", aMain = " + aMain);
      System.out.println(indent + "bSide = " + bSide);
      System.out.println(indent + "separator = " + separator);
      System.out.println(indent + "aMainNb = " + aMainNb);
      System.out.println(indent + "sFixed = " + sFixed);

      System.out.println(indent + minSeps.size() + " minSeps so far");
      
      ArrayList<XBitSet> fulls = g.fullComponents(separator);
      assert fulls.contains(aSide);
      assert fulls.contains(bSide);
    }

    assert sFixed.isSubset(separator);
    assert sFixed.cardinality() <= k;
//    assert separator.subtract(aNeighbors).isSubset(aMainNb);
    assert g.neighborSet(bSide).equals(separator);
    
    if (aMainNb.equals(separator)) {
      // never fragile
      return;
    }
    
    if (TRACE) {
      System.out.println(indent + "sFixed " + sFixed);
    }

    if (sFixed.equals(separator)) {
      assert !aMainNb.equals(separator);
      if (isFragile(separator)) {
        if (TRACE) {
          System.out.println(indent + "minSep added: " + separator);
        }
        minSeps.add(separator);
      }
      return;
    }
    
    int u = bestMainNb(aMainNb, sFixed, separator);
    if (u >= 0) {
      XBitSet aSide1 = aSide.addBit(u);
      XBitSet aMain1 = null;
      if (g.neighborSet[u].intersects(aSide.subtract(aMain).removeBit(a))) {
        ArrayList<XBitSet> components = g.componentsOf(aSide1.removeBit(a));
        for (XBitSet compo: components) {
          if (aMain.isSubset(compo)) {
            aMain1 = compo;
            break;
          }
        }
        assert aMain1 != null;
      }
      else {
        aMain1 = aMain.addBit(u);
      }
      XBitSet newNb = g.neighborSet[u].subtract(aSide).subtract(separator);
      generateFrom(
          aMain1, 
          aSide.addBit(u), 
          separator.removeBit(u).unionWith(newNb), 
          g.neighborSet(aMain1).removeBit(a), 
          sFixed, 
          indent + " ");
      if (sFixed.cardinality() < k) {
        generateFrom(
            aMain, 
            aSide, 
            separator,
            aMainNb, 
            sFixed.addBit(u), 
            indent + " ");
      }
      return;
    }
    u = bestFromRest(separator, sFixed);
    if (u < 0) {
      return;
    }

    if (TRACE) {
      System.out.println(indent + "branching on " + u + " from the rest");
    }
    XBitSet nb = g.neighborSet[u].subtract(separator).subtract(aSide);
    XBitSet separator1 = separator.removeBit(u).unionWith(nb);
    generateFrom(aMain, aSide.addBit(u), 
        separator1, aMainNb, sFixed, indent + " ");

    if (sFixed.cardinality() < k) {
      branch(aMain, aSide, bSide, separator, aMainNb, sFixed.addBit(u),
          indent + " ");
    }

  }
  
  int bestFromRest(XBitSet separator, XBitSet sFixed) {
    XBitSet aNbUndecided = separator.intersectWith(aNeighbors).subtract(sFixed);
    if (!aNbUndecided.isEmpty()) {
      return aNbUndecided.nextSetBit(0); 
    }
    XBitSet undecided = separator.subtract(sFixed); 
    assert !undecided.isEmpty();
    return undecided.nextSetBit(0);
  }

  int bestMainNb(XBitSet aMainNb, XBitSet sFixed, XBitSet separator) {
    int best = -1;
    int maxRed = 0;
    XBitSet gap = separator.subtract(aMainNb);
    for (int v: aMainNb.subtract(sFixed).toArray()) {
      int red = gap.intersectWith(g.neighborSet[v]).cardinality();
      if (best == -1 || red > maxRed) {
        best = v;
        maxRed = red;
      }
    }
    return best;
  }

  boolean isFragile(XBitSet minSep) {
    Minor minor = new Minor(g);
    minor = minor.contract(e.u, e.v);
    return minor.h.fullComponents(minSep.convert(minor.map)).size() < 2;
  }


}

