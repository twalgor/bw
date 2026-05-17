package tw.nice;

import tw.common.XBitSet;

public interface NodeMaker {
  NiceTDNode makeForgetNode(XBitSet bag, int forget, NiceTDNode child);
  NiceTDNode makeIntroduceNode(XBitSet bag, int introduce, NiceTDNode child);
  NiceTDNode makeJoinNode(XBitSet bag, NiceTDNode[] children);
  NiceTDNode makeLeafNode(XBitSet bag);
}
