package bw;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import bw.BranchDec.BDNode;
import tw.common.Graph;
import tw.common.Subgraph;
import tw.common.XBitSet;

public class Algorithm1 {

  Graph g;
  int width;
  BranchDec branchDec;

  Algorithm1(Graph g) {
    this.g = g;
  }
  
  public void decompose() {
    if (g.isStar()) {
      width = 1;
      branchDec = new BranchDec(g);
      BDNode bd = null;
      for (XBitSet e: allEdges()) {
        BDNode bd1 = branchDec.new BDNode(e);
        bd = branchDec.compose(bd1, bd);
      }
      branchDec.root = bd;
    }
    else {
      int v0 = 0;
      while (v0 < g.n && g.neighborSet[v0].cardinality() >= 2) {
        v0++;
      }
      if (v0 == g.n) {
        BlockDPWithoutRD0 bldp = new BlockDPWithoutRD0(g);
        bldp.decompose();
        width = bldp.k;
        branchDec = bldp.branchDec;
        return;
      }
      assert g.neighborSet[v0].cardinality() == 1;
      Subgraph sub = new Subgraph(g, g.all.removeBit(v0));
      Algorithm1 bw = new Algorithm1(sub.h);
      bw.decompose();
      width = bw.width;
      if (width == 1) {
        width = 2;
      }
      branchDec = new BranchDec(g);
      branchDec.root = branchDec.convert(bw.branchDec.root, sub.inv);
      int u = g.neighborSet[v0].nextSetBit(0);
      branchDec.hangALeaf(u, new XBitSet(new int[] {u, v0}));
    }
  }
 
  Set<XBitSet> allEdges() {
    Set<XBitSet> edges = new HashSet<>();
    for (int v = 0; v < g.n; v++) {
      for (int w: g.neighborSet[v].toArray()) {
        if (w > v) {
          edges.add(new XBitSet(new int[] {v, w}));
        }
      }
    }     
    return edges;
  }

  public static void main(String[] args) {
    if (args.length >= 2) {
      test(args[0], args[1]);
    }
    else if (args.length == 1) {
      test(args[0], null);
    }
    else {
//      String instanceName = "PasechnikGraph_1";
//      String instanceName = "WorldMap";
//      String instanceName = "CirculantGraph_20_5";
//      String instanceName = MarkstroemGraph";
//      String instanceName = "DorogovtsevGoltsevMendesGraph";
//      String instanceName = "SwitchedSquaredSkewHadamardMatrixGraph_3";
      String instanceName = "FriendshipGraph_10";   
      test("../instance/treewidthLib/" + instanceName + ".gr", instanceName + ".bd");
    }
  }
  
  static void test(String path, String outPath) {
    File file = new File(path);
    Graph g = Graph.readGraph(file);
    System.out.println(file.getName() + " read: n " + 
        g.n + " m " + g.numberOfEdges());

    long t0 = System.currentTimeMillis();
    ArrayList<XBitSet> components = g.componentsOf(g.all);
    
    BranchDec branchDec = new BranchDec(g);

    int width = 0;
    for (XBitSet component: components) {
//      System.out.println("component " + component);
      Subgraph sub = new Subgraph(g, component);
      Algorithm1 bw = new Algorithm1(sub.h);
      bw.decompose();
      if (bw.width> width) {
        width = bw.width;
      }
      assert bw.branchDec != null;
      branchDec.root = branchDec.compose(branchDec.root, branchDec.convert(bw.branchDec.root, sub.inv));
    }
    
    long t1 = System.currentTimeMillis();
    System.out.println("bw " + width + " " + (t1 - t0) + " millisecs");
//    System.out.println("bd.width " + branchDec.width());
    if (outPath != null) {
      branchDec.validate();
      File outFile = new File(outPath);
      PrintStream ps;
      try {
        ps = new PrintStream(new FileOutputStream(outFile));
        branchDec.root.printTree(0, ps);
        ps.close();
      } catch (FileNotFoundException e) {
        e.printStackTrace();
      }
    }
  }
}
