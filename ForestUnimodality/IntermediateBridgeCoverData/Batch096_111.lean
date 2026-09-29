import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band096 : Band CellKey where
  qlo := (22/51)
  qhi := (67/153)
  mlo := (3425373134328358208955223880597/200000000000000000000000000000)
  mhi := (48526119402985074626865671641791/1000000000000000000000000000000)
  cells := [(59,24),(99,24),(130,24)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 24

theorem band096_checked : band096.check rectangle=true := by decide +kernel
#print axioms band096_checked

def band097 : Band CellKey where
  qlo := (22/51)
  qhi := (67/153)
  mlo := (23977611940298507462686567164179/1000000000000000000000000000000)
  mhi := (48526119402985074626865671641791/1000000000000000000000000000000)
  cells := [(80,24),(99,24),(130,24)]
  lowerOrder := 80
  orderCap := 98
  rank := 21
  parentStrip := 24

theorem band097_checked : band097.check rectangle=true := by decide +kernel
#print axioms band097_checked

def band098 : Band CellKey where
  qlo := (22/51)
  qhi := (67/153)
  mlo := (28544776119402985074626865671641/1000000000000000000000000000000)
  mhi := (48526119402985074626865671641791/1000000000000000000000000000000)
  cells := [(99,24),(130,24)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 24

theorem band098_checked : band098.check rectangle=true := by decide +kernel
#print axioms band098_checked

def band099 : Band CellKey where
  qlo := (22/51)
  qhi := (67/153)
  mlo := (37679104477611940298507462686567/1000000000000000000000000000000)
  mhi := (48526119402985074626865671641791/1000000000000000000000000000000)
  cells := [(130,24)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 24

theorem band099_checked : band099.check rectangle=true := by decide +kernel
#print axioms band099_checked

def band100 : Band CellKey where
  qlo := (67/153)
  qhi := (4/9)
  mlo := (18/1)
  mhi := (765/16)
  cells := [(59,25),(99,25),(130,25)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 25

theorem band100_checked : band100.check rectangle=true := by decide +kernel
#print axioms band100_checked

def band101 : Band CellKey where
  qlo := (67/153)
  qhi := (4/9)
  mlo := (189/8)
  mhi := (765/16)
  cells := [(80,25),(99,25),(130,25)]
  lowerOrder := 80
  orderCap := 98
  rank := 21
  parentStrip := 25

theorem band101_checked : band101.check rectangle=true := by decide +kernel
#print axioms band101_checked

def band102 : Band CellKey where
  qlo := (67/153)
  qhi := (4/9)
  mlo := (225/8)
  mhi := (765/16)
  cells := [(99,25),(130,25)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 25

theorem band102_checked : band102.check rectangle=true := by decide +kernel
#print axioms band102_checked

def band103 : Band CellKey where
  qlo := (67/153)
  qhi := (4/9)
  mlo := (297/8)
  mhi := (765/16)
  cells := [(130,25)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 25

theorem band103_checked : band103.check rectangle=true := by decide +kernel
#print axioms band103_checked

def band104 : Band CellKey where
  qlo := (4/9)
  qhi := (301/666)
  mlo := (2212624584717607973421926910299/125000000000000000000000000000)
  mhi := (47018272425249169435215946843853/1000000000000000000000000000000)
  cells := [(59,26),(99,26),(130,26)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 26

theorem band104_checked : band104.check rectangle=true := by decide +kernel
#print axioms band104_checked

def band105 : Band CellKey where
  qlo := (4/9)
  qhi := (301/666)
  mlo := (23232558139534883720930232558139/1000000000000000000000000000000)
  mhi := (47018272425249169435215946843853/1000000000000000000000000000000)
  cells := [(80,26),(99,26),(130,26)]
  lowerOrder := 80
  orderCap := 98
  rank := 21
  parentStrip := 26

theorem band105_checked : band105.check rectangle=true := by decide +kernel
#print axioms band105_checked

def band106 : Band CellKey where
  qlo := (4/9)
  qhi := (301/666)
  mlo := (27657807308970099667774086378737/1000000000000000000000000000000)
  mhi := (47018272425249169435215946843853/1000000000000000000000000000000)
  cells := [(99,26),(130,26)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 26

theorem band106_checked : band106.check rectangle=true := by decide +kernel
#print axioms band106_checked

def band107 : Band CellKey where
  qlo := (4/9)
  qhi := (301/666)
  mlo := (36508305647840531561461794019933/1000000000000000000000000000000)
  mhi := (47018272425249169435215946843853/1000000000000000000000000000000)
  cells := [(130,26)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 26

theorem band107_checked : band107.check rectangle=true := by decide +kernel
#print axioms band107_checked

def band108 : Band CellKey where
  qlo := (301/666)
  qhi := (17/37)
  mlo := (3482352941176470588235294117647/200000000000000000000000000000)
  mhi := (185/4)
  cells := [(59,27),(59,28),(99,27),(130,27)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 27

theorem band108_checked : band108.check rectangle=true := by decide +kernel
#print axioms band108_checked

def band109 : Band CellKey where
  qlo := (301/666)
  qhi := (17/37)
  mlo := (11426470588235294117647058823529/500000000000000000000000000000)
  mhi := (185/4)
  cells := [(80,27),(99,27),(130,27)]
  lowerOrder := 80
  orderCap := 98
  rank := 21
  parentStrip := 27

theorem band109_checked : band109.check rectangle=true := by decide +kernel
#print axioms band109_checked

def band110 : Band CellKey where
  qlo := (301/666)
  qhi := (17/37)
  mlo := (27205882352941176470588235294117/1000000000000000000000000000000)
  mhi := (185/4)
  cells := [(99,27),(130,27)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 27

theorem band110_checked : band110.check rectangle=true := by decide +kernel
#print axioms band110_checked

def band111 : Band CellKey where
  qlo := (301/666)
  qhi := (17/37)
  mlo := (7182352941176470588235294117647/200000000000000000000000000000)
  mhi := (185/4)
  cells := [(130,27)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 27

theorem band111_checked : band111.check rectangle=true := by decide +kernel
#print axioms band111_checked

end ForestUnimodality.IntermediateBridgeCoverData

