package tw.lb;

import java.io.File;

import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import tw.common.Graph;
import tw.common.XBitSet;
import tw.sieve.SubblockSieve;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Queue;
import java.util.Random;

public class ACPPID {

  Graph g;
  int width; 
  Set<XBitSet> feasibles;
  Set<XBitSet> feasibles1;
  Queue<XBitSet> queue;
  SubblockSieve[] sieve;
  
  boolean countExceeded;
    
  public ACPPID(Graph g, int width) {
    this.g = g;
    this.width = width;
  }
  
  public int numberOfFeasiblesNotTrivialAdmissible() {
    int count = 0;
    for (XBitSet con: feasibles) {
      if (con.cardinality() < g.n - width) {
        count++;
      }
    }
    return count;
  }
  
  void generateFeasibles() {
    feasibles = new HashSet<>();
    queue = new LinkedList<>();
    sieve = new SubblockSieve[g.n];
    for (int v = 0; v < g.n; v++) {
      sieve[v] = new SubblockSieve(g, width + 1);
      if (g.neighborSet[v].cardinality() <= width) {
        XBitSet c = new XBitSet(g.n);
        c.set(v);
        queue.add(c);
        feasibles.add(c);
      }
    }
    
    while (!queue.isEmpty()) {
      XBitSet compo = queue.remove();
      XBitSet separator = g.neighborSet(compo);

      combineWith(compo, separator);

      for (int v = separator.nextSetBit(0); v >= 0; v = separator.nextSetBit(v + 1)) {
        sieve[v].add(compo, separator);
      }
    }
  }
  
  void combineWith(XBitSet component, XBitSet separator) {
    for (int v = separator.nextSetBit(0); v >= 0; v = separator.nextSetBit(v + 1)) {
      combineAt(v, 0, component, separator);
    }
  }
  
  void combineAt(int v, int maxMin, XBitSet combined, XBitSet separator) {
    if (combined.cardinality() >= g.n - width - 1) {
      return;
    }
    ArrayList<XBitSet> compos = g.separatedComponents(g.all.subtract(combined));
    for (XBitSet c: compos) {
      assert feasibles.contains(c): combined + ", " + c;
      assert g.neighborSet[v].intersects(combined);
    }
    XBitSet neighbors = separator.unionWith(g.neighborSet[v]);
    neighbors.andNot(combined);
    neighbors.clear(v);
    if (neighbors.cardinality() <= width) {
      XBitSet component = (XBitSet) combined.clone();
      component.set(v);
      assert g.neighborSet(component).equals(neighbors);
      if (feasibles.add(component)) {
        queue.add(component);
      }
    }
    
    XBitSet rest = g.all.subtract(combined.unionWith(separator));
    ArrayList<XBitSet> candidates = sieve[v].get(rest, separator);
    for (XBitSet cand: candidates) {
      if (cand.nextSetBit(0) < maxMin) {
        continue;
      }
      XBitSet sep = g.neighborSet(cand);
      XBitSet union = sep.unionWith(separator);
      assert union.cardinality() <= width + 1;
      XBitSet combined1 = combined.unionWith(cand);
      combineAt(v, cand.nextSetBit(0), combined1, union);
    }
  }
  
  void printFeasibles() {
    for (XBitSet feasible: feasibles) {
      System.out.println(feasible);
    }
  }
  
  void verify() {
    feasibles1 = new HashSet<>();
    XBitSet[] fa = new XBitSet[feasibles.size()];
    feasibles.toArray(fa);
    Arrays.sort(fa, XBitSet.cardinalityComparator);
    for (XBitSet compo: fa) {
      assert isFeasible(compo): compo + ", " + g.neighborSet(compo);
      feasibles1.add(compo);
    }
  }
  
  boolean isFeasible(XBitSet component) {
//    System.out.println("isFeasible? " + component);
    XBitSet separator = g.neighborSet(component);
    if (separator.cardinality() > width) {
      return false;
    }
    if (component.cardinality() + separator.cardinality() <= width + 1) {
      return true;
    }
    for (int v = component.nextSetBit(0); v >= 0;
        v = component.nextSetBit(v + 1)) {
      XBitSet extended = g.all.subtract(component);
      extended.set(v);
      ArrayList<XBitSet> components = g.separatedComponents(extended);
      boolean feasible = true;
      for (XBitSet compo: components) {
//        System.out.println("  v = " + v + ", compo = " + compo 
//            + ":" + feasibles1.contains(compo));
        if (!feasibles1.contains(compo)) {
          feasible = false;
          break;
        }
      }
      if (feasible) {
//        System.out.println("Feasible: " + component);
        return true;
      }
    }
//    System.out.println("Infeasible: " + component);
    return false;
  }

  static void test(String path, String name, int width) {
    Graph g = Graph.readGraph(path, name);
    ACPPID ap = new ACPPID(g, width);
    ap.generateFeasibles();
    ap.printFeasibles();
  }
  
  public static void main(String[] args) {
    test("../instance/grid", "troidal3_3", 5);
  }
}
