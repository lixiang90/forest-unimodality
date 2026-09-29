import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band240 : Band CellKey where
  qlo := (5227/10302)
  qhi := (3493/6868)
  mlo := (16712854279988548525622673919267/1000000000000000000000000000000)
  mhi := (23266344043763797017952411902033/500000000000000000000000000000)
  cells := [(59,112),(59,113),(99,72),(99,73),(130,77),(130,78)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 60

theorem band240_checked : band240.check rectangle=true := by decide +kernel
#print axioms band240_checked

def band241 : Band CellKey where
  qlo := (5227/10302)
  qhi := (3493/6868)
  mlo := (22611508731749212711136558831949/1000000000000000000000000000000)
  mhi := (23266344043763797017952411902033/500000000000000000000000000000)
  cells := [(80,93),(99,72),(99,73),(130,77),(130,78)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 60

theorem band241_checked : band241.check rectangle=true := by decide +kernel
#print axioms band241_checked

def band242 : Band CellKey where
  qlo := (5227/10302)
  qhi := (3493/6868)
  mlo := (27527054108216432865731462925851/1000000000000000000000000000000)
  mhi := (23266344043763797017952411902033/500000000000000000000000000000)
  cells := [(99,72),(99,73),(130,77),(130,78)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 60

theorem band242_checked : band242.check rectangle=true := by decide +kernel
#print axioms band242_checked

def band243 : Band CellKey where
  qlo := (5227/10302)
  qhi := (3493/6868)
  mlo := (291000286286859433152018322359/8000000000000000000000000000)
  mhi := (23266344043763797017952411902033/500000000000000000000000000000)
  cells := [(130,77),(130,78)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 60

theorem band243_checked : band243.check rectangle=true := by decide +kernel
#print axioms band243_checked

def band244 : Band CellKey where
  qlo := (3493/6868)
  qhi := (26/51)
  mlo := (4168269230769230769230769230769/250000000000000000000000000000)
  mhi := (929548248098527080409648867429/20000000000000000000000000000)
  cells := [(59,114),(59,115),(99,74),(99,75),(130,79),(130,80)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 61

theorem band244_checked : band244.check rectangle=true := by decide +kernel
#print axioms band244_checked

def band245 : Band CellKey where
  qlo := (3493/6868)
  qhi := (26/51)
  mlo := (5639423076923076923076923076923/250000000000000000000000000000)
  mhi := (929548248098527080409648867429/20000000000000000000000000000)
  cells := [(80,94),(99,74),(99,75),(130,79),(130,80)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 61

theorem band245_checked : band245.check rectangle=true := by decide +kernel
#print axioms band245_checked

def band246 : Band CellKey where
  qlo := (3493/6868)
  qhi := (26/51)
  mlo := (13730769230769230769230769230769/500000000000000000000000000000)
  mhi := (929548248098527080409648867429/20000000000000000000000000000)
  cells := [(99,74),(99,75),(130,79),(130,80)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 61

theorem band246_checked : band246.check rectangle=true := by decide +kernel
#print axioms band246_checked

def band247 : Band CellKey where
  qlo := (3493/6868)
  qhi := (26/51)
  mlo := (36288461538461538461538461538461/1000000000000000000000000000000)
  mhi := (929548248098527080409648867429/20000000000000000000000000000)
  cells := [(130,79),(130,80)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 61

theorem band247_checked : band247.check rectangle=true := by decide +kernel
#print axioms band247_checked

def band248 : Band CellKey where
  qlo := (26/51)
  qhi := (3579/7004)
  mlo := (8317127689298686784017882089969/500000000000000000000000000000)
  mhi := (46424473626837498404082298359341/1000000000000000000000000000000)
  cells := [(59,116),(59,117),(99,76),(99,77),(130,81),(130,82)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 62

theorem band248_checked : band248.check rectangle=true := by decide +kernel
#print axioms band248_checked

def band249 : Band CellKey where
  qlo := (26/51)
  qhi := (3579/7004)
  mlo := (2250516904163174070969544565521/100000000000000000000000000000)
  mhi := (46424473626837498404082298359341/1000000000000000000000000000000)
  cells := [(80,95),(99,76),(99,77),(130,81),(130,82)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 62

theorem band249_checked : band249.check rectangle=true := by decide +kernel
#print axioms band249_checked

def band250 : Band CellKey where
  qlo := (26/51)
  qhi := (3579/7004)
  mlo := (6849399273540094998602961721151/250000000000000000000000000000)
  mhi := (46424473626837498404082298359341/1000000000000000000000000000000)
  cells := [(99,76),(99,77),(130,81),(130,82)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 62

theorem band250_checked : band250.check rectangle=true := by decide +kernel
#print axioms band250_checked

def band251 : Band CellKey where
  qlo := (26/51)
  qhi := (3579/7004)
  mlo := (36203967588711930706901369097513/1000000000000000000000000000000)
  mhi := (46424473626837498404082298359341/1000000000000000000000000000000)
  cells := [(130,81),(130,82)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 62

theorem band251_checked : band251.check rectangle=true := by decide +kernel
#print axioms band251_checked

def band252 : Band CellKey where
  qlo := (3579/7004)
  qhi := (5381/10506)
  mlo := (2074451774763055194201821222821/125000000000000000000000000000)
  mhi := (23185323109505224613975699032871/500000000000000000000000000000)
  cells := [(59,118),(59,119),(99,78),(99,79),(130,83),(130,84)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 63

theorem band252_checked : band252.check rectangle=true := by decide +kernel
#print axioms band252_checked

def band253 : Band CellKey where
  qlo := (3579/7004)
  qhi := (5381/10506)
  mlo := (1122644489871771046273926779409/50000000000000000000000000000)
  mhi := (23185323109505224613975699032871/500000000000000000000000000000)
  cells := [(80,96),(99,78),(99,79),(130,83),(130,84)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 63

theorem band253_checked : band253.check rectangle=true := by decide +kernel
#print axioms band253_checked

def band254 : Band CellKey where
  qlo := (3579/7004)
  qhi := (5381/10506)
  mlo := (6833488199219475933841293439881/250000000000000000000000000000)
  mhi := (23185323109505224613975699032871/500000000000000000000000000000)
  cells := [(99,78),(99,79),(130,83),(130,84)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 63

theorem band254_checked : band254.check rectangle=true := by decide +kernel
#print axioms band254_checked

def band255 : Band CellKey where
  qlo := (3579/7004)
  qhi := (5381/10506)
  mlo := (18059933097937186396580561233971/500000000000000000000000000000)
  mhi := (23185323109505224613975699032871/500000000000000000000000000000)
  cells := [(130,83),(130,84)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 63

theorem band255_checked : band255.check rectangle=true := by decide +kernel
#print axioms band255_checked

end ForestUnimodality.IntermediateBridgeCoverData

