package profiling;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import tw.common.Graph;
import tw.common.TreeDecomposition;
import tw.common.XBitSet;

public class NiceTDBasic {
  static final boolean TRACE_DP = true;
  //  static final boolean TRACE_PRE_DP = true;
  static final boolean TRACE_PRE_DP = false;
  static final boolean TRACE_POST_DP = true;
  Graph g;
  TDNode root;

  enum NodeType {leaf, join, forget, introduce}

  NiceTDBasic(Graph g, TreeDecomposition td, int r) {
    this(g, td, r, false);
  }
  
  NiceTDBasic(Graph g, TreeDecomposition td, int r, boolean fatRoot) {
    this.g = g;
    root = translate(td, r, 0);
    if (!fatRoot) {
      while (!root.bag.isEmpty()) {
        int v = root.bag.nextSetBit(0);
        XBitSet bag1 = root.bag.removeBit(v);
        root = new ForgetNode(bag1, v, root);
      }
    }
    root.setParents(null);
  }

  TDNode translate(TreeDecomposition td, int b, int p) {
    XBitSet bag = new XBitSet(td.bags[b]);
    ArrayList<TDNode> children = new ArrayList<>();
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
      ArrayList<TDNode> children1 = new ArrayList<>();
      for (TDNode child: children) {
        children1.add(thread(bag, child));
      }
      return binalize(bag, children1);
    }
  }

  TDNode linearize(XBitSet bag) {
    if (bag.isEmpty()) {
      return new LeafNode(bag);
    }
    else {
      int v = bag.nextSetBit(0);
      TDNode child = linearize(bag.removeBit(v));
      TDNode node = new IntroduceNode(bag, v, child);
      return node;
    }
  }

  TDNode thread(XBitSet bag, TDNode child) {
    if (!bag.isSubset(child.bag)) {
      int v0 = bag.subtract(child.bag).nextSetBit(0);
      TDNode node = thread(bag.removeBit(v0), child);
      return new IntroduceNode(bag, v0, node);
    }
    else if (!child.bag.isSubset(bag)) {
      int v0 = child.bag.subtract(bag).nextSetBit(0);
      TDNode node = thread(bag.addBit(v0), child);
      return new ForgetNode(bag, v0, node);
    }
    else {
      return child;
    }
  }

  TDNode binalize(XBitSet bag, ArrayList<TDNode> children) {
    if (children.size() == 2) {
      TDNode[] childr = new TDNode[2];
      TDNode node = new JoinNode(bag, children.toArray(childr));
      return node;
    }
    else {
      TDNode child1 = children.get(0);
      children.remove(0);
      TDNode child2 = binalize(bag, children);
      TDNode node = new JoinNode(bag, new TDNode[] {child1, child2});
      return node;
    }
  }


  void dump() {
    root.dump(0);
  }

  String spaces(int d) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < d; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }

  class TDNode {
    TDNode parent;
    XBitSet bag;

    TDNode[] children;

    XBitSet verticesBelow;
    XBitSet chainsBelow;

    TDNode (XBitSet bag) {
      this.bag = bag;
    }

    void setParents(TDNode parent) {
      this.parent = parent;
      for (TDNode child: children) {
        child.setParents(this);
      }
    }

    int depth() {
      if (parent == null) {
        return 0;
      }
      else {
        return parent.depth() + 1;
      }
    }

    String indent() {
      return spaces(depth());
    }

    String spaces(int n) {
      StringBuilder sb = new StringBuilder();
      for (int i = 0; i < n; i++) {
        sb.append(" ");
      }
      return sb.toString();
    }

    NodeType nodeType() {
      // to be overridden
      return null;
    }

    void dump(int d) {
    }

    @Override
    public int hashCode() {
      return bag.hashCode();
    }
  }

  class ForgetNode extends TDNode {
    int forget;
    int fPos;
    ForgetNode(XBitSet bag, int forget, TDNode child) {
      super(bag);
      this.forget = forget;
      children = new TDNode[] {child};
    }

    @Override
    NodeType nodeType() {
      return NodeType.forget;
    }


    @Override
    void dump(int d) {
      System.out.println(spaces(d) + "forget " + forget + " " + bag);
      children[0].dump(d + 1);
    }
  }

  class IntroduceNode extends TDNode {
    int introduce;
    XBitSet internalChainVertices;
    int[] ica;
    boolean[] internalChainUsed;

    IntroduceNode(XBitSet bag, int introduce, TDNode child) {
      super(bag);
      this.introduce = introduce;
      children = new TDNode[] {child};
    }


    @Override
    NodeType nodeType() {
      return NodeType.introduce;
    }

    @Override
    void dump(int d) {
      System.out.println(spaces(d) + "introduce " + introduce + " " + bag);
      children[0].dump(d + 1);
    }

  }

  class JoinNode extends TDNode {
    JoinNode(XBitSet bag, TDNode[] children) {
      super(bag);
      this.children = children;
    }


    @Override
    NodeType nodeType() {
      return NodeType.join;
    }

    @Override
    void dump(int d) {
      System.out.println(spaces(d) + "join " + bag);
      children[0].dump(d + 1);
      children[1].dump(d + 1);
    }
  }

  class LeafNode extends TDNode {

    LeafNode(XBitSet bag) {
      super(bag);
      children = new TDNode[0];
    }

    @Override
    NodeType nodeType() {
      return NodeType.leaf;
    }

    @Override
    void dump(int d) {
      System.out.println(spaces(d) + "leaf " + bag);
    }    
  }

  int indexOf(int x, int[] a) {
    for (int i = 0; i < a.length; i++) {
      if (x == a[i]) {
        return i;
      }
    }
    return -1;
  }

}
