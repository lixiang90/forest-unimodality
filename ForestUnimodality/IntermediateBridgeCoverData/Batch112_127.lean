import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band112 : Band CellKey where
  qlo := (17/37)
  qhi := (1613/3478)
  mlo := (431246125232486050836949783013/25000000000000000000000000000)
  mhi := (45819900805951642901425914445133/1000000000000000000000000000000)
  cells := [(59,29),(99,28),(130,28)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 28

theorem band112_checked : band112.check rectangle=true := by decide +kernel
#print axioms band112_checked

def band113 : Band CellKey where
  qlo := (17/37)
  qhi := (1613/3478)
  mlo := (5929634221946683199008059516429/250000000000000000000000000000)
  mhi := (45819900805951642901425914445133/1000000000000000000000000000000)
  cells := [(80,28),(99,28),(130,28)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 28

theorem band113_checked : band113.check rectangle=true := by decide +kernel
#print axioms band113_checked

def band114 : Band CellKey where
  qlo := (17/37)
  qhi := (1613/3478)
  mlo := (26952882827030378177309361438313/1000000000000000000000000000000)
  mhi := (45819900805951642901425914445133/1000000000000000000000000000000)
  cells := [(99,28),(130,28)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 28

theorem band114_checked : band114.check rectangle=true := by decide +kernel
#print axioms band114_checked

def band115 : Band CellKey where
  qlo := (17/37)
  qhi := (1613/3478)
  mlo := (17788902665840049597024178549287/500000000000000000000000000000)
  mhi := (45819900805951642901425914445133/1000000000000000000000000000000)
  cells := [(130,28)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 28

theorem band115_checked : band115.check rectangle=true := by decide +kernel
#print axioms band115_checked

def band116 : Band CellKey where
  qlo := (1613/3478)
  qhi := (22/47)
  mlo := (17090909090909090909090909090909/1000000000000000000000000000000)
  mhi := (45397727272727272727272727272727/1000000000000000000000000000000)
  cells := [(59,30),(59,31),(99,29),(130,29)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 29

theorem band116_checked : band116.check rectangle=true := by decide +kernel
#print axioms band116_checked

def band117 : Band CellKey where
  qlo := (1613/3478)
  qhi := (22/47)
  mlo := (47/2)
  mhi := (45397727272727272727272727272727/1000000000000000000000000000000)
  cells := [(80,29),(99,29),(130,29)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 29

theorem band117_checked : band117.check rectangle=true := by decide +kernel
#print axioms band117_checked

def band118 : Band CellKey where
  qlo := (1613/3478)
  qhi := (22/47)
  mlo := (5340909090909090909090909090909/200000000000000000000000000000)
  mhi := (45397727272727272727272727272727/1000000000000000000000000000000)
  cells := [(99,29),(130,29)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 29

theorem band118_checked : band118.check rectangle=true := by decide +kernel
#print axioms band118_checked

def band119 : Band CellKey where
  qlo := (1613/3478)
  qhi := (22/47)
  mlo := (141/4)
  mhi := (45397727272727272727272727272727/1000000000000000000000000000000)
  cells := [(130,29)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 29

theorem band119_checked : band119.check rectangle=true := by decide +kernel
#print axioms band119_checked

def band120 : Band CellKey where
  qlo := (22/47)
  qhi := (1677/3572)
  mlo := (17039952295766249254621347644603/1000000000000000000000000000000)
  mhi := (45262373285629099582587954680977/1000000000000000000000000000000)
  cells := [(59,32),(99,30),(130,30)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 30

theorem band120_checked : band120.check rectangle=true := by decide +kernel
#print axioms band120_checked

def band121 : Band CellKey where
  qlo := (22/47)
  qhi := (1677/3572)
  mlo := (23429934406678592725104353011329/1000000000000000000000000000000)
  mhi := (45262373285629099582587954680977/1000000000000000000000000000000)
  cells := [(80,30),(99,30),(130,30)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 30

theorem band121_checked : band121.check rectangle=true := by decide +kernel
#print axioms band121_checked

def band122 : Band CellKey where
  qlo := (22/47)
  qhi := (1677/3572)
  mlo := (346124031007751937984496124031/12500000000000000000000000000)
  mhi := (45262373285629099582587954680977/1000000000000000000000000000000)
  cells := [(99,30),(130,30)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 30

theorem band122_checked : band122.check rectangle=true := by decide +kernel
#print axioms band122_checked

def band123 : Band CellKey where
  qlo := (22/47)
  qhi := (1677/3572)
  mlo := (17572450805008944543828264758497/500000000000000000000000000000)
  mhi := (45262373285629099582587954680977/1000000000000000000000000000000)
  cells := [(130,30)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 30

theorem band123_checked : band123.check rectangle=true := by decide +kernel
#print axioms band123_checked

def band124 : Band CellKey where
  qlo := (1677/3572)
  qhi := (841/1786)
  mlo := (3397859690844233055885850178359/200000000000000000000000000000)
  mhi := (45127824019024970273483947681331/1000000000000000000000000000000)
  cells := [(59,33),(59,34),(99,31),(130,31)]
  lowerOrder := 59
  orderCap := 79
  rank := 16
  parentStrip := 31

theorem band124_checked : band124.check rectangle=true := by decide +kernel
#print axioms band124_checked

def band125 : Band CellKey where
  qlo := (1677/3572)
  qhi := (841/1786)
  mlo := (11680142687277051129607609988109/500000000000000000000000000000)
  mhi := (45127824019024970273483947681331/1000000000000000000000000000000)
  cells := [(80,31),(99,31),(130,31)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 31

theorem band125_checked : band125.check rectangle=true := by decide +kernel
#print axioms band125_checked

def band126 : Band CellKey where
  qlo := (1677/3572)
  qhi := (841/1786)
  mlo := (27607609988109393579072532699167/1000000000000000000000000000000)
  mhi := (45127824019024970273483947681331/1000000000000000000000000000000)
  cells := [(99,31),(130,31)]
  lowerOrder := 99
  orderCap := 129
  rank := 26
  parentStrip := 31

theorem band126_checked : band126.check rectangle=true := by decide +kernel
#print axioms band126_checked

def band127 : Band CellKey where
  qlo := (1677/3572)
  qhi := (841/1786)
  mlo := (4380053507728894173602853745541/125000000000000000000000000000)
  mhi := (45127824019024970273483947681331/1000000000000000000000000000000)
  cells := [(130,31)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 31

theorem band127_checked : band127.check rectangle=true := by decide +kernel
#print axioms band127_checked

end ForestUnimodality.IntermediateBridgeCoverData

