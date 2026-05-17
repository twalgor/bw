package tw.nice;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import tw.common.Edge;
import tw.common.Graph;
import tw.common.XBitSet;

public abstract class NiceTDNode {
  public XBitSet bag;
  public NiceTDNode parent;
  public NiceTDNode[] children;
  
  public NiceTDNode(XBitSet bag) {
    this.bag = bag;
  }
  
  public String indent() {
    return spaces(depth());
  }
  
  private int depth() {
    if (parent == null) {
      return 0;
    }
    else {
      return parent.depth() + 1;
    }
  }
  
  public XBitSet setOfVerticesBelow() {
    XBitSet result = new XBitSet();
    for (NiceTDNode child: children) {
      result.or(child.setOfVerticesBelow());
      result.or(child.bag.subtract(bag));
    }
    return result;
  }
  
  public XBitSet unionBags() {
    XBitSet result = new XBitSet();
    for (NiceTDNode child: children) {
      result.or(child.unionBags());
    }
    result.or(bag);
    return result;
  }
  

  public Set<Edge> allEdges(Graph g){
    Set<Edge> result = new HashSet<>();
    for (NiceTDNode child: children) {
      result.addAll(child.allEdges(g));
    }
    for (int v: bag.toArray()) {
      for (int w: g.neighborSet[v].intersectWith(bag).toArray()) {
        if(v < w) {
          result.add(new Edge(v, w, g.n));
        }
      }
    }
    return result;
  }

  public void listNodes(ArrayList<NiceTDNode> list) {
    list.add(this);
    for (NiceTDNode child: children) {
      child.listNodes(list);
    }
  }
  
  private String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }
}
