import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band352 : Band CellKey where
  qlo := (11791/22366)
  qhi := (23607/44732)
  mlo := (17053755242089210827296988181471/1000000000000000000000000000000)
  mhi := (45710885975416998715111316511621/1000000000000000000000000000000)
  cells := [(59,165),(99,128),(130,135),(130,136),(130,137)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 88

theorem band352_checked : band352.check rectangle=true := by decide +kernel
#print axioms band352_checked

def band353 : Band CellKey where
  qlo := (11791/22366)
  qhi := (23607/44732)
  mlo := (11369170161392807218197992120981/500000000000000000000000000000)
  mhi := (45710885975416998715111316511621/1000000000000000000000000000000)
  cells := [(80,145),(99,128),(130,135),(130,136),(130,137)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 88

theorem band353_checked : band353.check rectangle=true := by decide +kernel
#print axioms band353_checked

def band354 : Band CellKey where
  qlo := (11791/22366)
  qhi := (23607/44732)
  mlo := (3434436819587410513830643453213/125000000000000000000000000000)
  mhi := (45710885975416998715111316511621/1000000000000000000000000000000)
  cells := [(99,128),(130,135),(130,136),(130,137)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 88

theorem band354_checked : band354.check rectangle=true := by decide +kernel
#print axioms band354_checked

def band355 : Band CellKey where
  qlo := (11791/22366)
  qhi := (23607/44732)
  mlo := (35054941330961155589443809039691/1000000000000000000000000000000)
  mhi := (45710885975416998715111316511621/1000000000000000000000000000000)
  cells := [(130,135),(130,136),(130,137)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 88

theorem band355_checked : band355.check rectangle=true := by decide +kernel
#print axioms band355_checked

def band356 : Band CellKey where
  qlo := (23607/44732)
  qhi := (94453/178928)
  mlo := (3409848284331889934676505775359/200000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(59,166),(99,129),(130,138),(130,139)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 89

theorem band356_checked : band356.check rectangle=true := by decide +kernel
#print axioms band356_checked

def band357 : Band CellKey where
  qlo := (23607/44732)
  qhi := (94453/178928)
  mlo := (22732321895545932897843371835727/1000000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(80,146),(99,129),(130,138),(130,139)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 89

theorem band357_checked : band357.check rectangle=true := by decide +kernel
#print axioms band357_checked

def band358 : Band CellKey where
  qlo := (23607/44732)
  qhi := (94453/178928)
  mlo := (429190973288302118513969910961/15625000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(99,129),(130,138),(130,139)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 89

theorem band358_checked : band358.check rectangle=true := by decide +kernel
#print axioms band358_checked

def band359 : Band CellKey where
  qlo := (23607/44732)
  qhi := (94453/178928)
  mlo := (35045662922299979884175198246747/1000000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(130,138),(130,139)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 89

theorem band359_checked : band359.check rectangle=true := by decide +kernel
#print axioms band359_checked

def band360 : Band CellKey where
  qlo := (94453/178928)
  qhi := (47239/89464)
  mlo := (17044729990050593789030250428671/1000000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(59,167),(99,130),(130,140),(130,141)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 89

theorem band360_checked : band360.check rectangle=true := by decide +kernel
#print axioms band360_checked

def band361 : Band CellKey where
  qlo := (94453/178928)
  qhi := (47239/89464)
  mlo := (22726306653400791718707000571561/1000000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(80,147),(99,130),(130,140),(130,141)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 89

theorem band361_checked : band361.check rectangle=true := by decide +kernel
#print axioms band361_checked

def band362 : Band CellKey where
  qlo := (94453/178928)
  qhi := (47239/89464)
  mlo := (6865238468214822498359406422659/250000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(99,130),(130,140),(130,141)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 89

theorem band362_checked : band362.check rectangle=true := by decide +kernel
#print axioms band362_checked

def band363 : Band CellKey where
  qlo := (94453/178928)
  qhi := (47239/89464)
  mlo := (35036389423992887233006625881157/1000000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(130,140),(130,141)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 89

theorem band363_checked : band363.check rectangle=true := by decide +kernel
#print axioms band363_checked

def band364 : Band CellKey where
  qlo := (47239/89464)
  qhi := (94503/178928)
  mlo := (2130027618170851718993047839751/125000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(59,168),(99,131),(130,142),(130,143),(130,144)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 89

theorem band364_checked : band364.check rectangle=true := by decide +kernel
#print axioms band364_checked

def band365 : Band CellKey where
  qlo := (47239/89464)
  qhi := (94503/178928)
  mlo := (22720294593822418335925843624011/1000000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(80,148),(99,131),(130,142),(130,143),(130,144)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 89

theorem band365_checked : band365.check rectangle=true := by decide +kernel
#print axioms band365_checked

def band366 : Band CellKey where
  qlo := (47239/89464)
  qhi := (94503/178928)
  mlo := (27453689300868755489243727712347/1000000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(99,131),(130,142),(130,143),(130,144)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 89

theorem band366_checked : band366.check rectangle=true := by decide +kernel
#print axioms band366_checked

def band367 : Band CellKey where
  qlo := (47239/89464)
  qhi := (94503/178928)
  mlo := (7005424166428578986910468450737/200000000000000000000000000000)
  mhi := (45686726706331366712396122639749/1000000000000000000000000000000)
  cells := [(130,142),(130,143),(130,144)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 89

theorem band367_checked : band367.check rectangle=true := by decide +kernel
#print axioms band367_checked

end ForestUnimodality.IntermediateBridgeCoverData

