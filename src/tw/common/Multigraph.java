package tw.common;

import java.util.Arrays;

public class Multigraph {
  public int n;
  int[][] adjacency;
  
  
  public Multigraph(int n) {
    this.n = n;
    adjacency = new int[n][n];
  }
  
  public Multigraph copy() {
    Multigraph g = new Multigraph(n);
    g.adjacency = new int[n][];
    for (int i = 0; i < n; i++) {
      g.adjacency[i] = Arrays.copyOf(adjacency[i], n);
    }
    return g;
  }
  
  public boolean areAdjacent(int u, int v) {
    return adjacency[u][v] > 0;
  }
  
  public void addEdge(int u, int v) {
    adjacency[u][v]++;
    adjacency[v][u]++;
  }

  public void removeEdge(int u, int v) {
    assert adjacency[u][v] > 0;
    adjacency[u][v]--;
    adjacency[v][u]--;
  }
  
  public boolean isConnected() {
    boolean[] mark = new boolean[n];
    search(0, mark);
    for (int i = 0; i < n; i++) {
      if (!mark[i]) {
        return false;
      }
    }
    return true;
  }
  
  void search(int v, boolean[] mark) {
    if (mark[v]) {
      return;
    }
    mark[v] = true;
    for (int u = 0; u < n; u++) {
      if (u != v && adjacency[v][u] > 0) {
        search(u, mark);
      }
    }
  }
  
  public boolean isSubgraphOf(Multigraph g) {
    for (int u = 0; u < n; u++) {
      for (int v = 0; v < n; v++) {
        if (adjacency[u][v] > g.adjacency[u][v]) {
          return false;
        }
      }
    }
    return true;
  }

  
  public Multigraph add(Multigraph g) {
    Multigraph added = new Multigraph(n);
    for (int u = 0; u < n; u++) {
      for (int v = 0; v < n; v++) {
        added.adjacency[u][v] = adjacency[u][v] + g.adjacency[u][v];
      }
    }
    return added;
  }
  
  @Override
  public boolean equals(Object x) {
    Multigraph g = (Multigraph) x;
    return Arrays.deepEquals(adjacency, g.adjacency);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    for (int v = 0; v < n; v++) {
      sb.append(v);
      for (int u = v + 1; u < n; u++) {
        if (adjacency[v][u] > 0) {
          sb.append(" " + u + "(" + adjacency[v][u] + ")" );
        }
      }
      sb.append("\n");
    }
    return sb.toString();
  }

}
