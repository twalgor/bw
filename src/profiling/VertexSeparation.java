package profiling;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import profiling.NiceTDBasic.NodeType;
import profiling.NiceTDBasic.TDNode;
import tw.common.Chordal;
import tw.common.Graph;
import tw.common.TreeDecomposition;
import tw.common.XBitSet;
import tw.decomposer.SemiPID;
import tw.greedy.MMAF;

public class VertexSeparation {
  static final boolean TRACE = true;
  //    static final boolean TRACE_TABLE = true;
  static final boolean TRACE_TABLE = false;

  Graph g;
  int n;
  int k;

  NiceTDBasic ntd;
  DPNode dpRoot;
  int nRelevants;
  int nProfiles;

  public VertexSeparation(Graph g, int k) {
    this.g = g;
    this.k = k;
    n = g.n;

    TreeDecomposition td = decompose1(g);

    if (TRACE) {
      System.out.println("VSep generator n " + n + " ne " + g.numberOfEdges() + 
          " k " + k + " width " + td.width + " nBags " + td.nb);
    }
    td.writeTo(System.out);
    NiceTDBasic ntd = new NiceTDBasic(g, td, 1, false);

    dpRoot = new DPNode(ntd.root, null);
    dpRoot.setVerticesBelow();
  }

  TreeDecomposition decompose(Graph h) {
    return SemiPID.decompose(h);
  }

  TreeDecomposition decompose1(Graph h) {
    Graph t = h.copy();
    MMAF mmaf = new MMAF(t);
    mmaf.triangulate();
    TreeDecomposition td = Chordal.chordalToTD(t);
    td.g = h;
    return td;
  }

  XBitSet parseXBitSet(String s) {
    s = s.substring(s.indexOf("{") + 1);
    s = s.substring(0, s.indexOf("}"));
    XBitSet set = new XBitSet();
    String[] t = s.split("\\,");
    for (String r: t) {
      int i = Integer.parseInt(r.trim());
      set.set(i);
    }
    return set;
  }

  void dp() {
    dpRoot.dp();

    System.out.println(dpRoot.profileMap.size() + " profiles at root");
    
    for (DPNode.Profile pf: dpRoot.profileMap.keySet()) {
      pf.listRelevants();
    }
    
    nRelevants = 0;
    dpRoot.count();
    
    System.out.println(nProfiles + " profiles and " + nRelevants + " relevants in total");

  }
  
  boolean separated(XBitSet vs1, XBitSet vs2) {
    return !vs2.intersects(g.neighborSet(vs1));
  } 


  class Separation {
    XBitSet[] part;

    Separation(XBitSet[] part) {
      this.part = part;
    }


    boolean isFeasible() {
      return part[0].intersectWith(part[1]).cardinality() <= k &&
          separated(part[0].subtract(part[1]),
              part[1].subtract(part[0]));
    }


    boolean isSorted() {
      return XBitSet.cardinalityComparator.compare(part[0], part[1]) <= 0;       
    }

    boolean isAllConnected() {
      return g.isConnected(part[0]) && g.isConnected(part[1]);
    }

    Separation unionWith(Separation separation) {
      XBitSet[] part1 = new XBitSet[2];
      for (int i = 0; i < 2; i++) {
        part1[i] = part[i].unionWith(separation.part[i]);
      }
      Separation separation1 = new Separation(part1);
      return separation1;
    }

    boolean isFull() {
      return part[0].unionWith(part[1]).equals(g.all);
    }

    Separation restrict(XBitSet vs) {
      return new Separation(new XBitSet[] {
          part[0].intersectWith(vs),
          part[1].intersectWith(vs)
      });
    }

    void validate() {
      assert isAllConnected();
      assert isFeasible();
    }

    @Override
    public int hashCode() {
      return Arrays.hashCode(part);
    }

    @Override
    public boolean equals(Object x) {
      Separation t = (Separation) x;
      return Arrays.equals(part, t.part);
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder();
      sb.append(Arrays.toString(part));
      return sb.toString();
    }

  }
  class DPNode {
    TDNode tdNode;
    DPNode parent;
    XBitSet bag;
    int[] va;
    DPNode[] children;
    int vi;
    int vf;

    XBitSet verticesBelow;

    Map<Profile, Profile> profileMap;
    Set<Profile> relevants;

    DPNode(TDNode tdNode, DPNode parent) {
      this.tdNode = tdNode;
      this.parent = parent;
      bag = tdNode.bag;
      va = bag.toArray();
      profileMap = new HashMap<>();

      children = new DPNode[tdNode.children.length];
      assert children.length <= 2;
      for (int i = 0; i < children.length; i++) {
        children[i] = new DPNode(tdNode.children[i], this);
        if (children.length == 2) {
          assert tdNode.nodeType() == NodeType.join;
          assert children[i].bag.equals(bag);
        }
      }
      if (nodeType() == NodeType.forget) {
        vf = ((NiceTDBasic.ForgetNode) tdNode).forget;
        assert children[0].bag.get(vf);
      }
      else if (nodeType() == NodeType.introduce) {
        vi = ((NiceTDBasic.IntroduceNode) tdNode).introduce;
        assert bag.get(vi);
      }
      if (TRACE) {
        System.out.println(indent(depth())+ this);
      }
    }

    void count() {
      nProfiles = profileMap.size();
      nRelevants = relevants.size();
      for (DPNode child: children) {
        child.count();
      }
    }

    class Profile {
      XBitSet[] vs;
      int nIntersec;
      Set<Profile[]> childProfiles;

      Profile(XBitSet[] vs, int nIntersec) {
        this.vs = vs;
        this.nIntersec = nIntersec;
      }
      
      boolean isFeasible() {
        return nIntersec <= k &&
            separated(vs[0].subtract(vs[0]), vs[1].subtract(vs[0]));
      }

      Profile register() {
        Profile pf = profileMap.get(this);
        if (pf != null) {
          return pf;
        }
        profileMap.put(this, this);
        return this;
      }

      void addChild(Profile pf) {
        if (childProfiles == null) {
          childProfiles = new HashSet<>();
        }
        childProfiles.add(new Profile[] {pf});
      }
      
      void addChildPair(Profile pf1, Profile pf2) { 
        if (childProfiles == null) {
          childProfiles = new HashSet<>();
        }
        childProfiles.add(new Profile[] {pf1, pf2});
      }
      
      void listRelevants() {
        DPNode.this.addRelevant(this);

        switch (DPNode.this.nodeType()) {
        case leaf:
          break;
        case introduce:
        case forget:
          for (Profile[] pfa: childProfiles) {
            pfa[0].listRelevants();
          }
          break;
        case join:
          for (Profile[] pfa: childProfiles) {
            pfa[0].listRelevants();
            pfa[1].listRelevants();
          }
          break;
        }
        
      }

      @Override
      public int hashCode() {
        return Arrays.hashCode(vs) + nIntersec;
      }
      @Override
      public boolean equals(Object x) {
        Profile pf = (Profile) x;
        return Arrays.equals(vs, pf.vs) &&
            nIntersec == pf.nIntersec;
      }

      @Override
      public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("vs " + Arrays.toString(vs));
        sb.append("nI " + nIntersec);
        return sb.toString();
      }
    }

    NodeType nodeType() {
      return tdNode.nodeType();
    }

    void addRelevant(Profile profile) {
      if (relevants == null) {
        relevants = new HashSet<>();
      }
      relevants.add(profile);
    }

    void dp() {
      if (TRACE) {
        System.out.println(indent(depth()) + tdNode.nodeType() + " bag " + tdNode.bag);
      }
      for (int i = 0; i < children.length; i++) {
        children[i].dp();
      }

      switch (nodeType()) {
      case leaf:
        dpLeaf();
        break;
      case introduce:
        dpIntroduce();
        break;
      case forget:
        dpForget();
        break;
      case join:
        dpJoin();
        break;
      }

      if (TRACE) {
        System.out.println(indent(depth()) + nodeType() + " exiting va " 
            + Arrays.toString(va));
        System.out.println(indent(depth()) + profileMap.size() + " profiles in table");
      }
      if (TRACE_TABLE) {
        for (Profile profile: profileMap.keySet()) {
          System.out.println(indent(depth()) + " " + profile);
        }
      }
    }

    void dpLeaf() {
      assert tdNode.bag.isEmpty();
      Profile pf = new Profile(new XBitSet[] {new XBitSet(), new XBitSet()}, 0);
      pf.register();
    }

    void dpIntroduce() {
      if (TRACE) {
        System.out.println(indent(depth()) +  "introduce " + vi);
      }

      assert nodeType() == NodeType.introduce;

      for (Profile cpf: children[0].profileMap.keySet()) {
        for (int i = 1; i < 4; i++) {
          XBitSet[] vs = new XBitSet[2];
          if (i == 1) {
            if (g.neighborSet[vi].intersects(cpf.vs[1].subtract(cpf.vs[0]))) {
              continue;
            }
            vs[0] = cpf.vs[0].addBit(vi);
            vs[1] = cpf.vs[1];
          }
          else if (i == 2) {
            if (g.neighborSet[vi].intersects(cpf.vs[0].subtract(cpf.vs[1]))) {
              continue;
            }
            vs[0] = cpf.vs[0];
            vs[1] = cpf.vs[1].addBit(vi);
          }
          else {
            assert i == 3;
            vs[0] = cpf.vs[0].addBit(i);
            vs[1] = cpf.vs[1].addBit(vi);
          }
          int nIntersec = cpf.nIntersec;
          if (i == 3) {
            nIntersec++;
            if (nIntersec > k) {
              continue;
            }
          }
          Profile pf = new Profile(vs, nIntersec);
          pf = pf.register();
          pf.addChild(cpf);
        }
      }
    }

    void dpForget() {
      int vf = ((NiceTDBasic.ForgetNode) tdNode).forget;
      assert children[0].bag.get(vf);
      if (TRACE) {
        System.out.println(indent(depth()) +  "forget " + vf);
      }
      for (Profile cpf: children[0].profileMap.keySet()) {
        assert cpf.isFeasible();
        if (TRACE_TABLE) {
          System.out.println(indent(depth()) + "forgetting from " + cpf);
        }
        XBitSet[] vs = new XBitSet[2];
        for (int i = 0; i < 2; i++) {
          if (cpf.vs[i].get(vf)) {
            vs[i] = cpf.vs[i].removeBit(vf);
          }
          else {
            vs[i] = cpf.vs[i];
          }
        }
        Profile pf = new Profile(vs, cpf.nIntersec);
        pf = pf.register();
        pf.addChild(cpf);
      }
    }
    
    class Vass {
      XBitSet[] vs;
      
      Vass(XBitSet[] vs) {
        this.vs = vs;
      }
      
      @Override
      public int hashCode() {
        return Arrays.hashCode(vs);
      }
      @Override
      public boolean equals(Object x) {
        Vass vass = (Vass) x;
        return Arrays.equals(vs, vass.vs);
      }
      
    }
    void dpJoin() {
      Map<Vass, Map<Profile, Profile>> smap1 = new HashMap<>();
      Map<Vass, Map<Profile, Profile>> smap2 = new HashMap<>();
      
      for (Profile pf: children[0].profileMap.keySet()) {
        putProfile(pf, smap1);
      }
      for (Profile pf: children[1].profileMap.keySet()) {
        putProfile(pf, smap2);
      }
      
      for (Vass vass: smap1.keySet()) {
        Map<Profile, Profile> map1 = smap1.get(vass);
        Map<Profile, Profile> map2 = smap2.get(vass);
        if (map2 == null) {
          continue;
        }
        for (Profile pf1: map1.keySet()) {
          for (Profile pf2: map2.keySet()) {
            Profile pf = new Profile(vass.vs, 
                pf1.nIntersec + pf2.nIntersec - vass.vs[0].intersectWith(vass.vs[1]).cardinality());
            if (pf.nIntersec <= k) {
              pf = pf.register();
              pf.addChildPair(pf1, pf2);
            }
          }
        }
      }
    }
    
    void putProfile(Profile pf, Map<Vass, Map<Profile, Profile>> smap) {
      Vass vass = new Vass(pf.vs);
      Map<Profile, Profile> map = smap.get(vass);
      if (map == null) {
        map = new HashMap<>();
        smap.put(vass, map);
      }
      map.put(pf, pf);
    }

    void setVerticesBelow() {
      for (DPNode child: children) {
        child.setVerticesBelow();
      }
      verticesBelow = new XBitSet(va);
      for (DPNode child: children) {
        verticesBelow.or(child.verticesBelow);
      }
      //      System.out.println(indent(depth()) + "verticesBelow " + verticesBelow);
    }

    int depth() {
      if (parent == null) {
        return 0;
      }
      else {
        return parent.depth() + 1;
      }
    }

    String indent(int d) {
      StringBuilder sb = new StringBuilder();
      sb.append(d + ":");
      for (int i = 0; i < d % 80; i++) {
        sb.append(" ");
      }
      return sb.toString();
    }

  }
}

