package bw;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.Set;

import tw.common.Graph;
import tw.common.XBitSet;

public class BranchDec {
  Graph g;
  BDNode root;
  

  BranchDec(Graph g) {
    this.g = g;
  }

  int width() {

    Set<XBitSet> all = allEdges();
    return root.width(all);
    
  }
  void validate() {
    Set<XBitSet> missing = missingEdges();
    if(!missing.isEmpty()) {
      System.out.println("missing " + missing);
    }
  }

  Set<XBitSet> missingEdges() {
    Set<XBitSet> edges = new HashSet<>();
    root.collectEdges(edges);
    Set<XBitSet> all = allEdges();
    all.removeAll(edges);

    return all;
  }


  void hangALeaf(int v, XBitSet e) {
    assert e.get(v);
    boolean b = root.hangALeaf(v, e);
    if (!b) {
      System.out.println("couldn't hang e " + e + " at " + v);
      root.printTree(0);
      
    }
    assert b;
  }
  
  BDNode bdOfEdgesIn(XBitSet vs, Set<XBitSet> remainingEdges) {
    return bdOfEdgesBetween(vs, vs, remainingEdges);
  }

  BDNode bdOfEdgesBetween(XBitSet vs1, XBitSet vs2, Set<XBitSet> remainingEdges) {
    if (vs1.isEmpty()) {
      return null;
    }
    int u = vs1.nextSetBit(0);
    BDNode bd1 = bdOfEdgesBetween(u, vs2, remainingEdges);
    BDNode bd2 = bdOfEdgesBetween(vs1.removeBit(u), vs2, remainingEdges);
    return compose(bd1, bd2);
  }


  BDNode bdOfEdgesBetween(int u, XBitSet vs, Set<XBitSet> remainingEdges) {
    if (vs.isEmpty()) {
      return null;
    }
    int v = vs.nextSetBit(0);
    if (g.areAdjacent(u, v)) {
      XBitSet e = new XBitSet(new int[] {u, v});
      if (remainingEdges.contains(e)) {
        remainingEdges.remove(e);

        return compose(new BDNode(e), 
            bdOfEdgesBetween(u, vs.removeBit(v), remainingEdges));
      }

      else {
        return bdOfEdgesBetween(u, vs.removeBit(v), remainingEdges);
      }
    }
    else {
      return bdOfEdgesBetween(u, vs.removeBit(v), remainingEdges);
    }
  }


  BDNode compose(BDNode bd1, BDNode bd2) {
    if (bd1 == null) {
      return bd2;
    }
    if (bd2 == null) {
      return bd1;
    }
    return new BDNode(new BDNode[] {bd1, bd2});
  }
  
  BDNode convert(BDNode node, int[] conv) {
    if (node.children == null) {
      return new BDNode(node.edge.convert(conv));
    }
    else {
      BDNode bd0 = convert(node.children[0], conv);
      BDNode bd1 = convert(node.children[1], conv);
      return compose(bd0, bd1);
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

  class BDNode {
    XBitSet edge;
    BDNode[] children;

    BDNode(XBitSet edge) {
      this.edge = edge;
    }

    BDNode(BDNode[] children) {
      this.children = children;
    }

    Set<XBitSet> lowSet() {
      Set<XBitSet> edges = new HashSet<>();
      collectEdges(edges);
      return edges;
    }
    
    XBitSet midSet() {
      Set<XBitSet> low = lowSet();
      Set<XBitSet> up = allEdges();
      up.removeAll(low);
      return vertices(low).intersectWith(vertices(up));
    }
    
    void collectEdges(Set<XBitSet> edges) {
      if (children == null) {
        assert edge != null;
        edges.add(edge);
      }
      else {
        for (BDNode ch: children) {
          ch.collectEdges(edges);
        }
      }
    }
    
    int width(Set<XBitSet> all) {
      if (children == null) {
        Set<XBitSet> up = new HashSet<>(all);
        up.remove(edge);
        return edge.intersectWith(vertices(up)).cardinality();
      }
      int width = 0;
      for(BDNode child: children) {
        int w = child.width(all);
        if (w > width) {
          width = w;
        }
      }
      Set<XBitSet> low = new HashSet<>();
      collectEdges(low);
      int w = midSet(low, all).cardinality();
      if (w > width) {
        width = w;
      }
      return width;
    }
    
    XBitSet midSet(Set<XBitSet> low, Set<XBitSet> all) {
      Set<XBitSet> up = new HashSet<>(all);
      up.removeAll(low);
      return vertices(low).intersectWith(vertices(up));
    }
    
    XBitSet vertices(Set<XBitSet> edges) {
      XBitSet vs = new XBitSet();
      for (XBitSet e: edges) {
        vs.or(e);
      }
      return vs;
    }

    boolean hangALeaf(int v, XBitSet e) {
      if (children == null) {
        if (edge.get(v)) {
          children = new BDNode[2];
          children[0] = new BDNode(edge);
          children[1] = new BDNode(e);
          edge = null;
          return true;
        }
        else {
          return false;
        }
      }
      else {
        boolean b = children[0].hangALeaf(v, e);
        if (b) {
          return true; 
        }
        return children[1].hangALeaf(v, e);
      }
    }
    
    public void printTree(int d, PrintStream ps) {
      if (children == null) {
        ps.println(spaces(d) + edge);
      }
      else {
        ps.println(spaces(d) + ":");
        children[0].printTree(d + 1, ps);
        children[1].printTree(d + 1, ps);
      }
      
    }
    public void printTree(int d) {
      printTree(d, System.out);
    }
  }

  static String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i  < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }

}
