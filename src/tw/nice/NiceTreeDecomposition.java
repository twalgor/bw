package tw.nice;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import tw.common.Edge;
import tw.common.Graph;
import tw.common.Subgraph;
import tw.common.TreeDecomposition;
import tw.common.XBitSet;

public class NiceTreeDecomposition {
  static final boolean TRACE_DP = true;
//  static final boolean TRACE_PRE_DP = true;
  static final boolean TRACE_PRE_DP = false;
  static final boolean TRACE_POST_DP = true;
  Graph g;
  public NiceTDNode root;
  NodeMaker nodeMaker;

  public NiceTreeDecomposition(Graph g, TreeDecomposition td, int r, NodeMaker nodeMaker) {
    this.g = g;
    this.nodeMaker = nodeMaker;
    root = translate(td, r, 0);
    while (!root.bag.isEmpty()) {
      int v = root.bag.nextSetBit(0);
      XBitSet bag1 = root.bag.removeBit(v);
      NiceTDNode root1 = nodeMaker.makeForgetNode(bag1, v, root);
      root.parent = root1;
      root = root1;
    }
  }

 
  NiceTDNode translate(TreeDecomposition td, int b, int p) {
    XBitSet bag = new XBitSet(td.bags[b]);
    ArrayList<NiceTDNode> children = new ArrayList<>();
    for (int b1: td.neighbor[b]) {
      if (b1 == p) {
        continue;
      }
      children.add(translate(td, b1, b));
    }
    if (children.size() == 0) {
      return linearize(bag);
    }
    else if (children.size() == 1) {
      return thread(bag, children.get(0));
    }
    else {
      ArrayList<NiceTDNode> children1 = new ArrayList<>();
      for (NiceTDNode child: children) {
        children1.add(thread(bag, child));
      }
      return binalize(bag, children1);
    }
  }

  NiceTDNode linearize(XBitSet bag) {
    if (bag.isEmpty()) {
      return nodeMaker.makeLeafNode(bag);
    }
    else {
      int v = bag.nextSetBit(0);
      NiceTDNode child = linearize(bag.removeBit(v));
      NiceTDNode node = nodeMaker.makeIntroduceNode(bag, v, child);
      child.parent = node;
      return node;
    }
  }

  NiceTDNode thread(XBitSet bag, NiceTDNode child) {
    if (!bag.isSubset(child.bag)) {
      int v0 = bag.subtract(child.bag).nextSetBit(0);
      NiceTDNode node = thread(bag.removeBit(v0), child);
      NiceTDNode node1 = nodeMaker.makeIntroduceNode(bag, v0, node); 
      node.parent = node1;
      return node1;
    }
    else if (!child.bag.isSubset(bag)) {
      int v0 = child.bag.subtract(bag).nextSetBit(0);
      NiceTDNode node = thread(bag.addBit(v0), child);
      NiceTDNode node1 = nodeMaker.makeForgetNode(bag, v0, node);
      node.parent = node1;
      return node1;
    }
    else {
      return child;
    }
  }

  NiceTDNode binalize(XBitSet bag, ArrayList<NiceTDNode> children) {
    if (children.size() == 2) {
      NiceTDNode[] childr = new NiceTDNode[2];
      children.toArray(childr);
      NiceTDNode node = nodeMaker.makeJoinNode(bag, childr); 
      childr[0].parent =  node;
      childr[1].parent =  node;
      return node;
    }
    else {
      NiceTDNode child1 = children.get(0);
      children.remove(0);
      NiceTDNode child2 = binalize(bag, children);
      NiceTDNode node = nodeMaker.makeJoinNode(bag, new NiceTDNode[] {child1, child2});
      child1.parent = node;
      child2.parent = node;
      return node;
    }
  }
  
  public void validate() {
    contition1();
    condition2();
    condition3();
  }
  
  private void contition1() {
    XBitSet union = root.unionBags();
    assert union.equals(g.all): "missing vertices " + g.all.subtract(union);
  }
  
  private void condition2() {
    Set<Edge> edges = root.allEdges(g);
    Set<Edge> missing = new HashSet<>(g.edgeList());
    missing.removeAll(edges);
    assert missing.isEmpty():"missing edges " + missing;
  }

  private void condition3() {
    ArrayList<NiceTDNode> nodeList = new ArrayList<>();
    root.listNodes(nodeList);
    int nn = nodeList.size();
    Map<NiceTDNode, Integer> nodeMap = new HashMap<>();
    for (int i = 0; i < nn; i++) {
      nodeMap.put(nodeList.get(i), i);
    }
    
    Graph tree = new Graph(nn);
    for (NiceTDNode node: nodeList) {
      if (node.parent != null) {
        tree.addEdge(nodeMap.get(node), nodeMap.get(node.parent));
      }
    }
    
    for (int v = 0; v < g.n; v++) {
      XBitSet s = new XBitSet();
      for (int i = 0; i < nn; i++) {
        if (nodeList.get(i).bag.get(v)) {
          s.set(i);
        }
      }
      Subgraph sub = new Subgraph(tree, s);
      assert sub.h.isConnected(sub.h.all): "subgraph for vertex " + v + " not connected";
    }
  }

  String spaces(int d) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < d; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }
  
  public   
  int indexOf(int x, int[] a) {
    for (int i = 0; i < a.length; i++) {
      if (x == a[i]) {
        return i;
      }
    }
    return -1;
  }
  
  int indexOf(Object x, Object[] a) {
    for (int i = 0; i < a.length; i++) {
      if (x == a[i]) {
        return i;
      }
    }
    return -1;
  }

}
