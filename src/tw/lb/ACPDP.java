package tw.lb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import tw.common.Graph;
import tw.common.XBitSet;

public class ACPDP {
  Graph g;
  int k;
  
  Set<XBitSet> connecteds;
  Set<XBitSet> feasibles;
  
  public ACPDP(Graph g, int k) {
    this.g = g;
    this.k = k;
  }
  
  void dp(Set<XBitSet> availableSeps) {
    feasibles = new HashSet<>();
    XBitSet[] ca = new XBitSet[connecteds.size()];
    connecteds.toArray(ca);
    Arrays.sort(ca, XBitSet.cardinalityComparator);
    
    for (XBitSet component: ca) {
      if (availableSeps != null) {
        XBitSet sep = g.neighborSet(component);
        if (!availableSeps.contains(sep)) {
          continue;
        }
      }
      for (int v = component.nextSetBit(0); v >= 0; v = component.nextSetBit(v + 1)) {
        ArrayList<XBitSet> compos = g.componentsOf(component.removeBit(v));
        boolean allFeasible = true;
        for (XBitSet compo: compos) {
          if (!feasibles.contains(compo)) {
            allFeasible = false;
            break;
          }
        }
        if (allFeasible) {
          feasibles.add(component);
          break;
        }
      }
    }
  }
  
  Set<XBitSet> safeSeps() {
    Set<XBitSet> safeSeps = new HashSet<>();
    for (XBitSet feasible: feasibles) {
      XBitSet sep = g.neighborSet(feasible);
      ArrayList<XBitSet> compos = g.separatedComponents(feasible.unionWith(sep));
      boolean allFeasible = true;
      for (XBitSet compo: compos) {
        if (!feasibles.contains(compo)) {
          allFeasible = false;
          break;
        }
      }
      if (allFeasible) {
        safeSeps.add(sep);
      }
    }
    return safeSeps;
  }
  
  void generateConnecteds() {
    connecteds = new HashSet<>();
    for (int a = 0; a < g.n; a++) {
      generateFrom(a, new XBitSet(new int[] {a}), g.neighborSet[a], new XBitSet());
    }
  }

  void generateFrom(int a, XBitSet component, XBitSet neighbors, XBitSet sFixed) {
    if (component.cardinality() * 2 + neighbors.cardinality() > g.n) {
      return;
    }
    if (neighbors.equals(sFixed)) {
      connecteds.add(component);
      return;
    }
    XBitSet toChoose = neighbors.subtract(sFixed);
    if (sFixed.cardinality() == k) {
      XBitSet compo1 = component.unionWith(toChoose);
      generateFrom(a, compo1, g.neighborSet(compo1), sFixed);
      return;
    }
    
    for (int v = toChoose.nextSetBit(0); v >= 0; v = toChoose.nextSetBit(v + 1)) {
      generateFrom(a, component, neighbors, sFixed.addBit(v));
      if (v > a) {
        XBitSet compo1 = component.addBit(v);
        generateFrom(a, compo1, g.neighborSet(compo1), sFixed);
      }
    }
  }
  
  static void test(String path, String name, int width) {
    Graph g = Graph.readGraph(path, name);
    ACPDP ap = new ACPDP(g, width);
    long t0 = 0;
    ap.generateConnecteds();
    System.out.println("connecteds: " + (System.currentTimeMillis() - t0) + " millisecs");
    for (XBitSet compo: ap.connecteds) {
      System.out.println(" " + compo + " " + g.neighborSet(compo));
    }
    ap.dp(null);
    System.out.println("feasibles: " + (System.currentTimeMillis() - t0) + " millisecs");
    for (XBitSet compo: ap.feasibles) {
      System.out.println(" " + compo + " " + g.neighborSet(compo));
    }

    Set<XBitSet> safeSeps = ap.safeSeps();
    System.out.println("safeSeps: " + (System.currentTimeMillis() - t0) + " millisecs");
    for (XBitSet sep: safeSeps) {
      System.out.println(" " + sep);
    }
  }
  
  public static void main(String[] args) {
//    test("../instance/grid", "troidal3_3", 5);
//    test("../instance/grid", "troidal4_4", 7);
    test("../instance/grid", "troidal5_5", 10);
  }
  
}
