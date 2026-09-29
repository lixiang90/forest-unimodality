import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band576 : Band CellKey where
  qlo := (33/53)
  qhi := (467/742)
  mlo := (471694325481798715203426124197/31250000000000000000000000000)
  mhi := (41654988910386904998234618051619/1000000000000000000000000000000)
  cells := [(59,221),(99,178),(130,233)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 120

theorem band576_checked : band576.check rectangle=true := by decide +kernel
#print axioms band576_checked

def band577 : Band CellKey where
  qlo := (33/53)
  qhi := (467/742)
  mlo := (4131049250535331905781584582441/200000000000000000000000000000)
  mhi := (41654988910386904998234618051619/1000000000000000000000000000000)
  cells := [(80,224),(99,178),(130,233)]
  lowerOrder := 80
  orderCap := 98
  rank := 26
  parentStrip := 120

theorem band577_checked : band577.check rectangle=true := by decide +kernel
#print axioms band577_checked

def band578 : Band CellKey where
  qlo := (33/53)
  qhi := (467/742)
  mlo := (12313704496788008565310492505353/500000000000000000000000000000)
  mhi := (41654988910386904998234618051619/1000000000000000000000000000000)
  cells := [(99,178),(130,233)]
  lowerOrder := 99
  orderCap := 129
  rank := 31
  parentStrip := 120

theorem band578_checked : band578.check rectangle=true := by decide +kernel
#print axioms band578_checked

def band579 : Band CellKey where
  qlo := (33/53)
  qhi := (467/742)
  mlo := (8142933618843683083511777301927/250000000000000000000000000000)
  mhi := (41654988910386904998234618051619/1000000000000000000000000000000)
  cells := [(130,233)]
  lowerOrder := 130
  orderCap := 169
  rank := 41
  parentStrip := 120

theorem band579_checked : band579.check rectangle=true := by decide +kernel
#print axioms band579_checked

def band580 : Band CellKey where
  qlo := (467/742)
  qhi := (236/371)
  mlo := (1866790254237288135593220338983/125000000000000000000000000000)
  mhi := (1657445851407740543727095014723/40000000000000000000000000000)
  cells := [(59,222),(99,179),(130,234)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 121

theorem band580_checked : band580.check rectangle=true := by decide +kernel
#print axioms band580_checked

def band581 : Band CellKey where
  qlo := (467/742)
  qhi := (236/371)
  mlo := (2554555084745762711864406779661/125000000000000000000000000000)
  mhi := (1657445851407740543727095014723/40000000000000000000000000000)
  cells := [(80,225),(99,179),(130,234)]
  lowerOrder := 80
  orderCap := 98
  rank := 26
  parentStrip := 121

theorem band581_checked : band581.check rectangle=true := by decide +kernel
#print axioms band581_checked

def band582 : Band CellKey where
  qlo := (467/742)
  qhi := (236/371)
  mlo := (4873305084745762711864406779661/200000000000000000000000000000)
  mhi := (1657445851407740543727095014723/40000000000000000000000000000)
  cells := [(99,179),(130,234)]
  lowerOrder := 99
  orderCap := 129
  rank := 31
  parentStrip := 121

theorem band582_checked : band582.check rectangle=true := by decide +kernel
#print axioms band582_checked

def band583 : Band CellKey where
  qlo := (467/742)
  qhi := (236/371)
  mlo := (16113347457627118644067796610169/500000000000000000000000000000)
  mhi := (1657445851407740543727095014723/40000000000000000000000000000)
  cells := [(130,234)]
  lowerOrder := 130
  orderCap := 169
  rank := 41
  parentStrip := 121

theorem band583_checked : band583.check rectangle=true := by decide +kernel
#print axioms band583_checked

def band584 : Band CellKey where
  qlo := (236/371)
  qhi := (9/14)
  mlo := (14777777777777777777777777777777/1000000000000000000000000000000)
  mhi := (644073695044650172703389484177/15625000000000000000000000000)
  cells := [(59,223),(99,180),(130,235)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 122

theorem band584_checked : band584.check rectangle=true := by decide +kernel
#print axioms band584_checked

def band585 : Band CellKey where
  qlo := (236/371)
  qhi := (9/14)
  mlo := (10111111111111111111111111111111/500000000000000000000000000000)
  mhi := (644073695044650172703389484177/15625000000000000000000000000)
  cells := [(80,226),(99,180),(130,235)]
  lowerOrder := 80
  orderCap := 98
  rank := 26
  parentStrip := 122

theorem band585_checked : band585.check rectangle=true := by decide +kernel
#print axioms band585_checked

def band586 : Band CellKey where
  qlo := (236/371)
  qhi := (9/14)
  mlo := (3111111111111111111111111111111/125000000000000000000000000000)
  mhi := (644073695044650172703389484177/15625000000000000000000000000)
  cells := [(99,180),(130,235)]
  lowerOrder := 99
  orderCap := 129
  rank := 32
  parentStrip := 122

theorem band586_checked : band586.check rectangle=true := by decide +kernel
#print axioms band586_checked

def band587 : Band CellKey where
  qlo := (236/371)
  qhi := (9/14)
  mlo := (3986111111111111111111111111111/125000000000000000000000000000)
  mhi := (644073695044650172703389484177/15625000000000000000000000000)
  cells := [(130,235)]
  lowerOrder := 130
  orderCap := 169
  rank := 41
  parentStrip := 122

theorem band587_checked : band587.check rectangle=true := by decide +kernel
#print axioms band587_checked

def band588 : Band CellKey where
  qlo := (9/14)
  qhi := (41/63)
  mlo := (3649390243902439024390243902439/250000000000000000000000000000)
  mhi := (40933124174714097886579939645583/1000000000000000000000000000000)
  cells := [(59,224),(99,181),(130,236)]
  lowerOrder := 59
  orderCap := 79
  rank := 19
  parentStrip := 123

theorem band588_checked : band588.check rectangle=true := by decide +kernel
#print axioms band588_checked

def band589 : Band CellKey where
  qlo := (9/14)
  qhi := (41/63)
  mlo := (499390243902439024390243902439/25000000000000000000000000000)
  mhi := (40933124174714097886579939645583/1000000000000000000000000000000)
  cells := [(80,227),(99,181),(130,236)]
  lowerOrder := 80
  orderCap := 98
  rank := 26
  parentStrip := 123

theorem band589_checked : band589.check rectangle=true := by decide +kernel
#print axioms band589_checked

def band590 : Band CellKey where
  qlo := (9/14)
  qhi := (41/63)
  mlo := (3073170731707317073170731707317/125000000000000000000000000000)
  mhi := (40933124174714097886579939645583/1000000000000000000000000000000)
  cells := [(99,181),(130,236)]
  lowerOrder := 99
  orderCap := 129
  rank := 32
  parentStrip := 123

theorem band590_checked : band590.check rectangle=true := by decide +kernel
#print axioms band590_checked

def band591 : Band CellKey where
  qlo := (9/14)
  qhi := (41/63)
  mlo := (63/2)
  mhi := (40933124174714097886579939645583/1000000000000000000000000000000)
  cells := [(130,236)]
  lowerOrder := 130
  orderCap := 169
  rank := 41
  parentStrip := 123

theorem band591_checked : band591.check rectangle=true := by decide +kernel
#print axioms band591_checked

end ForestUnimodality.IntermediateBridgeCoverData

