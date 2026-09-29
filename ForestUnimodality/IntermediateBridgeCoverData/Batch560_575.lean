import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band560 : Band CellKey where
  qlo := (3/5)
  qhi := (123/203)
  mlo := (7839430894308943089430894308943/500000000000000000000000000000)
  mhi := (21237212827920694231148535443559/500000000000000000000000000000)
  cells := [(59,217),(99,174),(130,229)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 116

theorem band560_checked : band560.check rectangle=true := by decide +kernel
#print axioms band560_checked

def band561 : Band CellKey where
  qlo := (3/5)
  qhi := (123/203)
  mlo := (1289380081300813008130081300813/62500000000000000000000000000)
  mhi := (21237212827920694231148535443559/500000000000000000000000000000)
  cells := [(80,220),(99,174),(130,229)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 116

theorem band561_checked : band561.check rectangle=true := by decide +kernel
#print axioms band561_checked

def band562 : Band CellKey where
  qlo := (3/5)
  qhi := (123/203)
  mlo := (2558130081300813008130081300813/100000000000000000000000000000)
  mhi := (21237212827920694231148535443559/500000000000000000000000000000)
  cells := [(99,174),(130,229)]
  lowerOrder := 99
  orderCap := 129
  rank := 31
  parentStrip := 116

theorem band562_checked : band562.check rectangle=true := by decide +kernel
#print axioms band562_checked

def band563 : Band CellKey where
  qlo := (3/5)
  qhi := (123/203)
  mlo := (33008130081300813008130081300813/1000000000000000000000000000000)
  mhi := (21237212827920694231148535443559/500000000000000000000000000000)
  cells := [(130,229)]
  lowerOrder := 130
  orderCap := 169
  rank := 40
  parentStrip := 116

theorem band563_checked : band563.check rectangle=true := by decide +kernel
#print axioms band563_checked

def band564 : Band CellKey where
  qlo := (123/203)
  qhi := (63/103)
  mlo := (7765873015873015873015873015873/500000000000000000000000000000)
  mhi := (42282647772660323435816934804827/1000000000000000000000000000000)
  cells := [(59,218),(99,175),(130,230)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 117

theorem band564_checked : band564.check rectangle=true := by decide +kernel
#print axioms band564_checked

def band565 : Band CellKey where
  qlo := (123/203)
  qhi := (63/103)
  mlo := (20436507936507936507936507936507/1000000000000000000000000000000)
  mhi := (42282647772660323435816934804827/1000000000000000000000000000000)
  cells := [(80,221),(99,175),(130,230)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 117

theorem band565_checked : band565.check rectangle=true := by decide +kernel
#print axioms band565_checked

def band566 : Band CellKey where
  qlo := (123/203)
  qhi := (63/103)
  mlo := (25341269841269841269841269841269/1000000000000000000000000000000)
  mhi := (42282647772660323435816934804827/1000000000000000000000000000000)
  cells := [(99,175),(130,230)]
  lowerOrder := 99
  orderCap := 129
  rank := 31
  parentStrip := 117

theorem band566_checked : band566.check rectangle=true := by decide +kernel
#print axioms band566_checked

def band567 : Band CellKey where
  qlo := (123/203)
  qhi := (63/103)
  mlo := (8174603174603174603174603174603/250000000000000000000000000000)
  mhi := (42282647772660323435816934804827/1000000000000000000000000000000)
  cells := [(130,230)]
  lowerOrder := 130
  orderCap := 169
  rank := 40
  parentStrip := 117

theorem band567_checked : band567.check rectangle=true := by decide +kernel
#print axioms band567_checked

def band568 : Band CellKey where
  qlo := (63/103)
  qhi := (129/209)
  mlo := (3847868217054263565891472868217/250000000000000000000000000000)
  mhi := (21049375029339949552647351896941/500000000000000000000000000000)
  cells := [(59,219),(99,176),(130,231)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 118

theorem band568_checked : band568.check rectangle=true := by decide +kernel
#print axioms band568_checked

def band569 : Band CellKey where
  qlo := (63/103)
  qhi := (129/209)
  mlo := (316436531007751937984496124031/15625000000000000000000000000)
  mhi := (21049375029339949552647351896941/500000000000000000000000000000)
  cells := [(80,222),(99,176),(130,231)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 118

theorem band569_checked : band569.check rectangle=true := by decide +kernel
#print axioms band569_checked

def band570 : Band CellKey where
  qlo := (63/103)
  qhi := (129/209)
  mlo := (251124031007751937984496124031/10000000000000000000000000000)
  mhi := (21049375029339949552647351896941/500000000000000000000000000000)
  cells := [(99,176),(130,231)]
  lowerOrder := 99
  orderCap := 129
  rank := 31
  parentStrip := 118

theorem band570_checked : band570.check rectangle=true := by decide +kernel
#print axioms band570_checked

def band571 : Band CellKey where
  qlo := (63/103)
  qhi := (129/209)
  mlo := (1296124031007751937984496124031/40000000000000000000000000000)
  mhi := (21049375029339949552647351896941/500000000000000000000000000000)
  cells := [(130,231)]
  lowerOrder := 130
  orderCap := 169
  rank := 40
  parentStrip := 118

theorem band571_checked : band571.check rectangle=true := by decide +kernel
#print axioms band571_checked

def band572 : Band CellKey where
  qlo := (129/209)
  qhi := (33/53)
  mlo := (610303030303030303030303030303/40000000000000000000000000000)
  mhi := (41922252087453942940438786968883/1000000000000000000000000000000)
  cells := [(59,220),(99,177),(130,232)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 119

theorem band572_checked : band572.check rectangle=true := by decide +kernel
#print axioms band572_checked

def band573 : Band CellKey where
  qlo := (129/209)
  qhi := (33/53)
  mlo := (20075757575757575757575757575757/1000000000000000000000000000000)
  mhi := (41922252087453942940438786968883/1000000000000000000000000000000)
  cells := [(80,223),(99,177),(130,232)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 119

theorem band573_checked : band573.check rectangle=true := by decide +kernel
#print axioms band573_checked

def band574 : Band CellKey where
  qlo := (129/209)
  qhi := (33/53)
  mlo := (24893939393939393939393939393939/1000000000000000000000000000000)
  mhi := (41922252087453942940438786968883/1000000000000000000000000000000)
  cells := [(99,177),(130,232)]
  lowerOrder := 99
  orderCap := 129
  rank := 31
  parentStrip := 119

theorem band574_checked : band574.check rectangle=true := by decide +kernel
#print axioms band574_checked

def band575 : Band CellKey where
  qlo := (129/209)
  qhi := (33/53)
  mlo := (8030303030303030303030303030303/250000000000000000000000000000)
  mhi := (41922252087453942940438786968883/1000000000000000000000000000000)
  cells := [(130,232)]
  lowerOrder := 130
  orderCap := 169
  rank := 40
  parentStrip := 119

theorem band575_checked : band575.check rectangle=true := by decide +kernel
#print axioms band575_checked

end ForestUnimodality.IntermediateBridgeCoverData

