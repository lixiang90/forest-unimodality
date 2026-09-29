import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band544 : Band CellKey where
  qlo := (653/1128)
  qhi := (7/12)
  mlo := (15428571428571428571428571428571/1000000000000000000000000000000)
  mhi := (21667869661569756293475226172301/500000000000000000000000000000)
  cells := [(59,213),(99,170),(130,225)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 112

theorem band544_checked : band544.check rectangle=true := by decide +kernel
#print axioms band544_checked

def band545 : Band CellKey where
  qlo := (653/1128)
  qhi := (7/12)
  mlo := (21428571428571428571428571428571/1000000000000000000000000000000)
  mhi := (21667869661569756293475226172301/500000000000000000000000000000)
  cells := [(80,216),(99,170),(130,225)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 112

theorem band545_checked : band545.check rectangle=true := by decide +kernel
#print axioms band545_checked

def band546 : Band CellKey where
  qlo := (653/1128)
  qhi := (7/12)
  mlo := (5142857142857142857142857142857/200000000000000000000000000000)
  mhi := (21667869661569756293475226172301/500000000000000000000000000000)
  cells := [(99,170),(130,225)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 112

theorem band546_checked : band546.check rectangle=true := by decide +kernel
#print axioms band546_checked

def band547 : Band CellKey where
  qlo := (653/1128)
  qhi := (7/12)
  mlo := (33428571428571428571428571428571/1000000000000000000000000000000)
  mhi := (21667869661569756293475226172301/500000000000000000000000000000)
  cells := [(130,225)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 112

theorem band547_checked : band547.check rectangle=true := by decide +kernel
#print axioms band547_checked

def band548 : Band CellKey where
  qlo := (7/12)
  qhi := (53/90)
  mlo := (1528301886792452830188679245283/100000000000000000000000000000)
  mhi := (10772735796769720442651675532471/250000000000000000000000000000)
  cells := [(59,214),(99,171),(130,226)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 113

theorem band548_checked : band548.check rectangle=true := by decide +kernel
#print axioms band548_checked

def band549 : Band CellKey where
  qlo := (7/12)
  qhi := (53/90)
  mlo := (2653301886792452830188679245283/125000000000000000000000000000)
  mhi := (10772735796769720442651675532471/250000000000000000000000000000)
  cells := [(80,217),(99,171),(130,226)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 113

theorem band549_checked : band549.check rectangle=true := by decide +kernel
#print axioms band549_checked

def band550 : Band CellKey where
  qlo := (7/12)
  qhi := (53/90)
  mlo := (6367924528301886792452830188679/250000000000000000000000000000)
  mhi := (10772735796769720442651675532471/250000000000000000000000000000)
  cells := [(99,171),(130,226)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 113

theorem band550_checked : band550.check rectangle=true := by decide +kernel
#print axioms band550_checked

def band551 : Band CellKey where
  qlo := (7/12)
  qhi := (53/90)
  mlo := (8278301886792452830188679245283/250000000000000000000000000000)
  mhi := (10772735796769720442651675532471/250000000000000000000000000000)
  cells := [(130,226)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 113

theorem band551_checked : band551.check rectangle=true := by decide +kernel
#print axioms band551_checked

def band552 : Band CellKey where
  qlo := (53/90)
  qhi := (107/180)
  mlo := (15981308411214953271028037383177/1000000000000000000000000000000)
  mhi := (10722754911771359510444054600299/250000000000000000000000000000)
  cells := [(59,215),(99,172),(130,227)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 114

theorem band552_checked : band552.check rectangle=true := by decide +kernel
#print axioms band552_checked

def band553 : Band CellKey where
  qlo := (53/90)
  qhi := (107/180)
  mlo := (21028037383177570093457943925233/1000000000000000000000000000000)
  mhi := (10722754911771359510444054600299/250000000000000000000000000000)
  cells := [(80,218),(99,172),(130,227)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 114

theorem band553_checked : band553.check rectangle=true := by decide +kernel
#print axioms band553_checked

def band554 : Band CellKey where
  qlo := (53/90)
  qhi := (107/180)
  mlo := (630841121495327102803738317757/25000000000000000000000000000)
  mhi := (10722754911771359510444054600299/250000000000000000000000000000)
  cells := [(99,172),(130,227)]
  lowerOrder := 99
  orderCap := 129
  rank := 30
  parentStrip := 114

theorem band554_checked : band554.check rectangle=true := by decide +kernel
#print axioms band554_checked

def band555 : Band CellKey where
  qlo := (53/90)
  qhi := (107/180)
  mlo := (8200934579439252336448598130841/250000000000000000000000000000)
  mhi := (10722754911771359510444054600299/250000000000000000000000000000)
  cells := [(130,227)]
  lowerOrder := 130
  orderCap := 169
  rank := 39
  parentStrip := 114

theorem band555_checked : band555.check rectangle=true := by decide +kernel
#print axioms band555_checked

def band556 : Band CellKey where
  qlo := (107/180)
  qhi := (3/5)
  mlo := (15833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (213469264417556709431485063733/5000000000000000000000000000)
  cells := [(59,216),(99,173),(130,228)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 115

theorem band556_checked : band556.check rectangle=true := by decide +kernel
#print axioms band556_checked

def band557 : Band CellKey where
  qlo := (107/180)
  qhi := (3/5)
  mlo := (20833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (213469264417556709431485063733/5000000000000000000000000000)
  cells := [(80,219),(99,173),(130,228)]
  lowerOrder := 80
  orderCap := 98
  rank := 25
  parentStrip := 115

theorem band557_checked : band557.check rectangle=true := by decide +kernel
#print axioms band557_checked

def band558 : Band CellKey where
  qlo := (107/180)
  qhi := (3/5)
  mlo := (25833333333333333333333333333333/1000000000000000000000000000000)
  mhi := (213469264417556709431485063733/5000000000000000000000000000)
  cells := [(99,173),(130,228)]
  lowerOrder := 99
  orderCap := 129
  rank := 31
  parentStrip := 115

theorem band558_checked : band558.check rectangle=true := by decide +kernel
#print axioms band558_checked

def band559 : Band CellKey where
  qlo := (107/180)
  qhi := (3/5)
  mlo := (33333333333333333333333333333333/1000000000000000000000000000000)
  mhi := (213469264417556709431485063733/5000000000000000000000000000)
  cells := [(130,228)]
  lowerOrder := 130
  orderCap := 169
  rank := 40
  parentStrip := 115

theorem band559_checked : band559.check rectangle=true := by decide +kernel
#print axioms band559_checked

end ForestUnimodality.IntermediateBridgeCoverData

