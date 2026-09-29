import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band064 : Band CellKey where
  qlo := (19/51)
  qhi := (97/255)
  mlo := (19716494845360824742268041237113/1000000000000000000000000000000)
  mhi := (27931701030927835051546391752577/500000000000000000000000000000)
  cells := [(59,16),(99,16),(130,16)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 16

theorem band064_checked : band064.check rectangle=true := by decide +kernel
#print axioms band064_checked

def band065 : Band CellKey where
  qlo := (19/51)
  qhi := (97/255)
  mlo := (6572164948453608247422680412371/250000000000000000000000000000)
  mhi := (27931701030927835051546391752577/500000000000000000000000000000)
  cells := [(80,16),(99,16),(130,16)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 16

theorem band065_checked : band065.check rectangle=true := by decide +kernel
#print axioms band065_checked

def band066 : Band CellKey where
  qlo := (19/51)
  qhi := (97/255)
  mlo := (6572164948453608247422680412371/200000000000000000000000000000)
  mhi := (27931701030927835051546391752577/500000000000000000000000000000)
  cells := [(99,16),(130,16)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 16

theorem band066_checked : band066.check rectangle=true := by decide +kernel
#print axioms band066_checked

def band067 : Band CellKey where
  qlo := (19/51)
  qhi := (97/255)
  mlo := (43376288659793814432989690721649/1000000000000000000000000000000)
  mhi := (27931701030927835051546391752577/500000000000000000000000000000)
  cells := [(130,16)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 16

theorem band067_checked : band067.check rectangle=true := by decide +kernel
#print axioms band067_checked

def band068 : Band CellKey where
  qlo := (97/255)
  qhi := (33/85)
  mlo := (19318181818181818181818181818181/1000000000000000000000000000000)
  mhi := (3420928030303030303030303030303/62500000000000000000000000000)
  cells := [(59,17),(99,17),(130,17)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 17

theorem band068_checked : band068.check rectangle=true := by decide +kernel
#print axioms band068_checked

def band069 : Band CellKey where
  qlo := (97/255)
  qhi := (33/85)
  mlo := (1030303030303030303030303030303/40000000000000000000000000000)
  mhi := (3420928030303030303030303030303/62500000000000000000000000000)
  cells := [(80,17),(99,17),(130,17)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 17

theorem band069_checked : band069.check rectangle=true := by decide +kernel
#print axioms band069_checked

def band070 : Band CellKey where
  qlo := (97/255)
  qhi := (33/85)
  mlo := (32196969696969696969696969696969/1000000000000000000000000000000)
  mhi := (3420928030303030303030303030303/62500000000000000000000000000)
  cells := [(99,17),(130,17)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 17

theorem band070_checked : band070.check rectangle=true := by decide +kernel
#print axioms band070_checked

def band071 : Band CellKey where
  qlo := (97/255)
  qhi := (33/85)
  mlo := (85/2)
  mhi := (3420928030303030303030303030303/62500000000000000000000000000)
  cells := [(130,17)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 17

theorem band071_checked : band071.check rectangle=true := by decide +kernel
#print axioms band071_checked

def band072 : Band CellKey where
  qlo := (33/85)
  qhi := (101/255)
  mlo := (18935643564356435643564356435643/1000000000000000000000000000000)
  mhi := (5365099009900990099009900990099/100000000000000000000000000000)
  cells := [(59,18),(99,18),(130,18)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 18

theorem band072_checked : band072.check rectangle=true := by decide +kernel
#print axioms band072_checked

def band073 : Band CellKey where
  qlo := (33/85)
  qhi := (101/255)
  mlo := (6311881188118811881188118811881/250000000000000000000000000000)
  mhi := (5365099009900990099009900990099/100000000000000000000000000000)
  cells := [(80,18),(99,18),(130,18)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 18

theorem band073_checked : band073.check rectangle=true := by decide +kernel
#print axioms band073_checked

def band074 : Band CellKey where
  qlo := (33/85)
  qhi := (101/255)
  mlo := (6311881188118811881188118811881/200000000000000000000000000000)
  mhi := (5365099009900990099009900990099/100000000000000000000000000000)
  cells := [(99,18),(130,18)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 18

theorem band074_checked : band074.check rectangle=true := by decide +kernel
#print axioms band074_checked

def band075 : Band CellKey where
  qlo := (33/85)
  qhi := (101/255)
  mlo := (8331683168316831683168316831683/200000000000000000000000000000)
  mhi := (5365099009900990099009900990099/100000000000000000000000000000)
  cells := [(130,18)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 18

theorem band075_checked : band075.check rectangle=true := by decide +kernel
#print axioms band075_checked

def band076 : Band CellKey where
  qlo := (101/255)
  qhi := (103/255)
  mlo := (9283980582524271844660194174757/500000000000000000000000000000)
  mhi := (52609223300970873786407766990291/1000000000000000000000000000000)
  cells := [(59,19),(99,19),(130,19)]
  lowerOrder := 59
  orderCap := 79
  rank := 15
  parentStrip := 19

theorem band076_checked : band076.check rectangle=true := by decide +kernel
#print axioms band076_checked

def band077 : Band CellKey where
  qlo := (101/255)
  qhi := (103/255)
  mlo := (24757281553398058252427184466019/1000000000000000000000000000000)
  mhi := (52609223300970873786407766990291/1000000000000000000000000000000)
  cells := [(80,19),(99,19),(130,19)]
  lowerOrder := 80
  orderCap := 98
  rank := 20
  parentStrip := 19

theorem band077_checked : band077.check rectangle=true := by decide +kernel
#print axioms band077_checked

def band078 : Band CellKey where
  qlo := (101/255)
  qhi := (103/255)
  mlo := (7736650485436893203883495145631/250000000000000000000000000000)
  mhi := (52609223300970873786407766990291/1000000000000000000000000000000)
  cells := [(99,19),(130,19)]
  lowerOrder := 99
  orderCap := 129
  rank := 25
  parentStrip := 19

theorem band078_checked : band078.check rectangle=true := by decide +kernel
#print axioms band078_checked

def band079 : Band CellKey where
  qlo := (101/255)
  qhi := (103/255)
  mlo := (10212378640776699029126213592233/250000000000000000000000000000)
  mhi := (52609223300970873786407766990291/1000000000000000000000000000000)
  cells := [(130,19)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 19

theorem band079_checked : band079.check rectangle=true := by decide +kernel
#print axioms band079_checked

end ForestUnimodality.IntermediateBridgeCoverData

