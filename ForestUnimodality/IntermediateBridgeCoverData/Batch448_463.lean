import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band448 : Band CellKey where
  qlo := (24257/45582)
  qhi := (32351/60776)
  mlo := (4226948162344286111712157274891/250000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(59,189),(99,152),(130,203),(130,204)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 97

theorem band448_checked : band448.check rectangle=true := by decide +kernel
#print axioms band448_checked

def band449 : Band CellKey where
  qlo := (24257/45582)
  qhi := (32351/60776)
  mlo := (11271861766251429631232419399709/500000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(80,169),(99,152),(130,203),(130,204)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 97

theorem band449_checked : band449.check rectangle=true := by decide +kernel
#print axioms band449_checked

def band450 : Band CellKey where
  qlo := (24257/45582)
  qhi := (32351/60776)
  mlo := (27240332601774288275478346882631/1000000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(99,152),(130,203),(130,204)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 97

theorem band450_checked : band450.check rectangle=true := by decide +kernel
#print axioms band450_checked

def band451 : Band CellKey where
  qlo := (24257/45582)
  qhi := (32351/60776)
  mlo := (35694228926462860498902661432413/1000000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(130,203),(130,204)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 97

theorem band451_checked : band451.check rectangle=true := by decide +kernel
#print axioms band451_checked

def band452 : Band CellKey where
  qlo := (32351/60776)
  qhi := (48539/91164)
  mlo := (16903438472156410309235872185253/1000000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(59,190),(99,153),(130,205),(130,206)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 97

theorem band452_checked : band452.check rectangle=true := by decide +kernel
#print axioms band452_checked

def band453 : Band CellKey where
  qlo := (32351/60776)
  qhi := (48539/91164)
  mlo := (22537917962875213745647829580337/1000000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(80,170),(99,153),(130,205),(130,206)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 97

theorem band453_checked : band453.check rectangle=true := by decide +kernel
#print axioms band453_checked

def band454 : Band CellKey where
  qlo := (32351/60776)
  qhi := (48539/91164)
  mlo := (27233317538474216609324460742907/1000000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(99,153),(130,205),(130,206)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 97

theorem band454_checked : band454.check rectangle=true := by decide +kernel
#print axioms band454_checked

def band455 : Band CellKey where
  qlo := (32351/60776)
  qhi := (48539/91164)
  mlo := (17842518387276210881971198417767/500000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(130,205),(130,206)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 97

theorem band455_checked : band455.check rectangle=true := by decide +kernel
#print axioms band455_checked

def band456 : Band CellKey where
  qlo := (48539/91164)
  qhi := (97103/182328)
  mlo := (2112385817122025066166853753231/125000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(59,191),(99,154),(130,207),(130,208)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 97

theorem band456_checked : band456.check rectangle=true := by decide +kernel
#print axioms band456_checked

def band457 : Band CellKey where
  qlo := (48539/91164)
  qhi := (97103/182328)
  mlo := (22532115382634934039113106701131/1000000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(80,171),(99,154),(130,207),(130,208)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 97

theorem band457_checked : band457.check rectangle=true := by decide +kernel
#print axioms band457_checked

def band458 : Band CellKey where
  qlo := (48539/91164)
  qhi := (97103/182328)
  mlo := (68065765218376363243154176493/2500000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(99,154),(130,207),(130,208)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 97

theorem band458_checked : band458.check rectangle=true := by decide +kernel
#print axioms band458_checked

def band459 : Band CellKey where
  qlo := (48539/91164)
  qhi := (97103/182328)
  mlo := (285406794846709164495432684881/8000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(130,207),(130,208)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 97

theorem band459_checked : band459.check rectangle=true := by decide +kernel
#print axioms band459_checked

def band460 : Band CellKey where
  qlo := (97103/182328)
  qhi := (57/107)
  mlo := (3378947368421052631578947368421/200000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(59,192),(99,155),(130,209),(130,210)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 97

theorem band460_checked : band460.check rectangle=true := by decide +kernel
#print axioms band460_checked

def band461 : Band CellKey where
  qlo := (97103/182328)
  qhi := (57/107)
  mlo := (22526315789473684210526315789473/1000000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(80,172),(99,155),(130,209),(130,210)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 97

theorem band461_checked : band461.check rectangle=true := by decide +kernel
#print axioms band461_checked

def band462 : Band CellKey where
  qlo := (97103/182328)
  qhi := (57/107)
  mlo := (13609649122807017543859649122807/500000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(99,155),(130,209),(130,210)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 97

theorem band462_checked : band462.check rectangle=true := by decide +kernel
#print axioms band462_checked

def band463 : Band CellKey where
  qlo := (97103/182328)
  qhi := (57/107)
  mlo := (17833333333333333333333333333333/500000000000000000000000000000)
  mhi := (45497940775901266402749485533109/1000000000000000000000000000000)
  cells := [(130,209),(130,210)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 97

theorem band463_checked : band463.check rectangle=true := by decide +kernel
#print axioms band463_checked

end ForestUnimodality.IntermediateBridgeCoverData

