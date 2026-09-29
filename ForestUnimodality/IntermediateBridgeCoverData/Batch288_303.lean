import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band288 : Band CellKey where
  qlo := (11153/21528)
  qhi := (22331/43056)
  mlo := (16388697326586359768931082351887/1000000000000000000000000000000)
  mhi := (46108445526827864511054105015143/1000000000000000000000000000000)
  cells := [(59,136),(59,137),(99,96),(99,97),(130,101),(130,102)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 72

theorem band288_checked : band288.check rectangle=true := by decide +kernel
#print axioms band288_checked

def band289 : Band CellKey where
  qlo := (11153/21528)
  qhi := (22331/43056)
  mlo := (11086471720926066902512202767453/500000000000000000000000000000)
  mhi := (46108445526827864511054105015143/1000000000000000000000000000000)
  cells := [(80,107),(80,108),(99,96),(99,97),(130,101),(130,102)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 72

theorem band289_checked : band289.check rectangle=true := by decide +kernel
#print axioms band289_checked

def band290 : Band CellKey where
  qlo := (11153/21528)
  qhi := (22331/43056)
  mlo := (1118287582284716313644709148717/40000000000000000000000000000)
  mhi := (46108445526827864511054105015143/1000000000000000000000000000000)
  cells := [(99,96),(99,97),(130,101),(130,102)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 72

theorem band290_checked : band290.check rectangle=true := by decide +kernel
#print axioms band290_checked

def band291 : Band CellKey where
  qlo := (11153/21528)
  qhi := (22331/43056)
  mlo := (8917379427701401638977206573821/250000000000000000000000000000)
  mhi := (46108445526827864511054105015143/1000000000000000000000000000000)
  cells := [(130,101),(130,102)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 72

theorem band291_checked : band291.check rectangle=true := by decide +kernel
#print axioms band291_checked

def band292 : Band CellKey where
  qlo := (22331/43056)
  qhi := (27/52)
  mlo := (1637037037037037037037037037037/100000000000000000000000000000)
  mhi := (23041343196720453962719357369241/500000000000000000000000000000)
  cells := [(59,138),(59,139),(99,98),(99,99),(130,103),(130,104)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 73

theorem band292_checked : band292.check rectangle=true := by decide +kernel
#print axioms band292_checked

def band293 : Band CellKey where
  qlo := (22331/43056)
  qhi := (27/52)
  mlo := (5537037037037037037037037037037/250000000000000000000000000000)
  mhi := (23041343196720453962719357369241/500000000000000000000000000000)
  cells := [(80,109),(80,110),(99,98),(99,99),(130,103),(130,104)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 73

theorem band293_checked : band293.check rectangle=true := by decide +kernel
#print axioms band293_checked

def band294 : Band CellKey where
  qlo := (22331/43056)
  qhi := (27/52)
  mlo := (1117037037037037037037037037037/40000000000000000000000000000)
  mhi := (23041343196720453962719357369241/500000000000000000000000000000)
  cells := [(99,98),(99,99),(130,103),(130,104)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 73

theorem band294_checked : band294.check rectangle=true := by decide +kernel
#print axioms band294_checked

def band295 : Band CellKey where
  qlo := (22331/43056)
  qhi := (27/52)
  mlo := (35629629629629629629629629629629/1000000000000000000000000000000)
  mhi := (23041343196720453962719357369241/500000000000000000000000000000)
  cells := [(130,103),(130,104)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 73

theorem band295_checked : band295.check rectangle=true := by decide +kernel
#print axioms band295_checked

def band296 : Band CellKey where
  qlo := (27/52)
  qhi := (22597/43472)
  mlo := (16352259149444616542018852060007/1000000000000000000000000000000)
  mhi := (23028731350119208306140866961749/500000000000000000000000000000)
  cells := [(59,140),(59,141),(99,100),(99,101),(130,105),(130,106)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 74

theorem band296_checked : band296.check rectangle=true := by decide +kernel
#print axioms band296_checked

def band297 : Band CellKey where
  qlo := (27/52)
  qhi := (22597/43472)
  mlo := (1382727795725096251714829402133/62500000000000000000000000000)
  mhi := (23028731350119208306140866961749/500000000000000000000000000000)
  cells := [(80,111),(80,112),(99,100),(99,101),(130,105),(130,106)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 74

theorem band297_checked : band297.check rectangle=true := by decide +kernel
#print axioms band297_checked

def band298 : Band CellKey where
  qlo := (27/52)
  qhi := (22597/43472)
  mlo := (3486878789219807939106961101031/125000000000000000000000000000)
  mhi := (23028731350119208306140866961749/500000000000000000000000000000)
  cells := [(99,100),(99,101),(130,105),(130,106)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 74

theorem band298_checked : band298.check rectangle=true := by decide +kernel
#print axioms band298_checked

def band299 : Band CellKey where
  qlo := (27/52)
  qhi := (22597/43472)
  mlo := (8897552772491923706686728326769/250000000000000000000000000000)
  mhi := (23028731350119208306140866961749/500000000000000000000000000000)
  cells := [(130,105),(130,106)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 74

theorem band299_checked : band299.check rectangle=true := by decide +kernel
#print axioms band299_checked

def band300 : Band CellKey where
  qlo := (22597/43472)
  qhi := (11311/21736)
  mlo := (8167093979312173989921315533551/500000000000000000000000000000)
  mhi := (46032034350087633013374905849549/1000000000000000000000000000000)
  cells := [(59,142),(59,143),(99,102),(99,103),(130,107),(130,108)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 75

theorem band300_checked : band300.check rectangle=true := by decide +kernel
#print axioms band300_checked

def band301 : Band CellKey where
  qlo := (22597/43472)
  qhi := (11311/21736)
  mlo := (22099195473432941384492971443727/1000000000000000000000000000000)
  mhi := (46032034350087633013374905849549/1000000000000000000000000000000)
  cells := [(80,113),(80,114),(99,102),(99,103),(130,107),(130,108)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 75

theorem band301_checked : band301.check rectangle=true := by decide +kernel
#print axioms band301_checked

def band302 : Band CellKey where
  qlo := (22597/43472)
  qhi := (11311/21736)
  mlo := (27864202988241534789143311820351/1000000000000000000000000000000)
  mhi := (46032034350087633013374905849549/1000000000000000000000000000000)
  cells := [(99,102),(99,103),(130,107),(130,108)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 75

theorem band302_checked : band302.check rectangle=true := by decide +kernel
#print axioms band302_checked

def band303 : Band CellKey where
  qlo := (22597/43472)
  qhi := (11311/21736)
  mlo := (35550879674652992662010432322517/1000000000000000000000000000000)
  mhi := (46032034350087633013374905849549/1000000000000000000000000000000)
  cells := [(130,107),(130,108)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 75

theorem band303_checked : band303.check rectangle=true := by decide +kernel
#print axioms band303_checked

end ForestUnimodality.IntermediateBridgeCoverData

