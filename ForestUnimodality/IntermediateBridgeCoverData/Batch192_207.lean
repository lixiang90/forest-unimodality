import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band192 : Band CellKey where
  qlo := (4777/9702)
  qhi := (3193/6468)
  mlo := (17218290009395552771688067647979/1000000000000000000000000000000)
  mhi := (22648149329516413239370375365133/500000000000000000000000000000)
  cells := [(59,72),(59,73),(59,74),(59,75),(99,53),(99,54),(130,59)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 48

theorem band192_checked : band192.check rectangle=true := by decide +kernel
#print axioms band192_checked

def band193 : Band CellKey where
  qlo := (4777/9702)
  qhi := (3193/6468)
  mlo := (23295333542123394926401503288443/1000000000000000000000000000000)
  mhi := (22648149329516413239370375365133/500000000000000000000000000000)
  cells := [(80,71),(80,72),(80,73),(99,53),(99,54),(130,59)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 48

theorem band193_checked : band193.check rectangle=true := by decide +kernel
#print axioms band193_checked

def band194 : Band CellKey where
  qlo := (4777/9702)
  qhi := (3193/6468)
  mlo := (5469339179455057939242092076417/200000000000000000000000000000)
  mhi := (22648149329516413239370375365133/500000000000000000000000000000)
  cells := [(99,53),(99,54),(130,59)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 48

theorem band194_checked : band194.check rectangle=true := by decide +kernel
#print axioms band194_checked

def band195 : Band CellKey where
  qlo := (4777/9702)
  qhi := (3193/6468)
  mlo := (3544942060757907923582837456937/100000000000000000000000000000)
  mhi := (22648149329516413239370375365133/500000000000000000000000000000)
  cells := [(130,59)]
  lowerOrder := 130
  orderCap := 169
  rank := 35
  parentStrip := 48

theorem band195_checked : band195.check rectangle=true := by decide +kernel
#print axioms band195_checked

def band196 : Band CellKey where
  qlo := (3193/6468)
  qhi := (49/99)
  mlo := (4293367346938775510204081632653/250000000000000000000000000000)
  mhi := (22784908551023603929514179614769/500000000000000000000000000000)
  cells := [(59,76),(59,77),(59,78),(59,79),(99,55),(130,60),(130,61)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 49

theorem band196_checked : band196.check rectangle=true := by decide +kernel
#print axioms band196_checked

def band197 : Band CellKey where
  qlo := (3193/6468)
  qhi := (49/99)
  mlo := (11617346938775510204081632653061/500000000000000000000000000000)
  mhi := (22784908551023603929514179614769/500000000000000000000000000000)
  cells := [(80,74),(80,75),(80,76),(80,77),(99,55),(130,60),(130,61)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 49

theorem band197_checked : band197.check rectangle=true := by decide +kernel
#print axioms band197_checked

def band198 : Band CellKey where
  qlo := (3193/6468)
  qhi := (49/99)
  mlo := (14142857142857142857142857142857/500000000000000000000000000000)
  mhi := (22784908551023603929514179614769/500000000000000000000000000000)
  cells := [(99,55),(130,60),(130,61)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 49

theorem band198_checked : band198.check rectangle=true := by decide +kernel
#print axioms band198_checked

def band199 : Band CellKey where
  qlo := (3193/6468)
  qhi := (49/99)
  mlo := (17678571428571428571428571428571/500000000000000000000000000000)
  mhi := (22784908551023603929514179614769/500000000000000000000000000000)
  cells := [(130,60),(130,61)]
  lowerOrder := 130
  orderCap := 169
  rank := 35
  parentStrip := 49

theorem band199_checked : band199.check rectangle=true := by decide +kernel
#print axioms band199_checked

def band200 : Band CellKey where
  qlo := (49/99)
  qhi := (131/264)
  mlo := (17129770992366412213740458015267/1000000000000000000000000000000)
  mhi := (5730282892195045957314223399279/125000000000000000000000000000)
  cells := [(59,80),(59,81),(59,82),(59,83),(99,56),(130,62),(130,63)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 50

theorem band200_checked : band200.check rectangle=true := by decide +kernel
#print axioms band200_checked

def band201 : Band CellKey where
  qlo := (49/99)
  qhi := (131/264)
  mlo := (2896946564885496183206106870229/125000000000000000000000000000)
  mhi := (5730282892195045957314223399279/125000000000000000000000000000)
  cells := [(80,78),(99,56),(130,62),(130,63)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 50

theorem band201_checked : band201.check rectangle=true := by decide +kernel
#print axioms band201_checked

def band202 : Band CellKey where
  qlo := (49/99)
  qhi := (131/264)
  mlo := (28213740458015267175572519083969/1000000000000000000000000000000)
  mhi := (5730282892195045957314223399279/125000000000000000000000000000)
  cells := [(99,56),(130,62),(130,63)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 50

theorem band202_checked : band202.check rectangle=true := by decide +kernel
#print axioms band202_checked

def band203 : Band CellKey where
  qlo := (49/99)
  qhi := (131/264)
  mlo := (35267175572519083969465648854961/1000000000000000000000000000000)
  mhi := (5730282892195045957314223399279/125000000000000000000000000000)
  cells := [(130,62),(130,63)]
  lowerOrder := 130
  orderCap := 169
  rank := 35
  parentStrip := 50

theorem band203_checked : band203.check rectangle=true := by decide +kernel
#print axioms band203_checked

def band204 : Band CellKey where
  qlo := (131/264)
  qhi := (197/396)
  mlo := (1708629441624365482233502538071/100000000000000000000000000000)
  mhi := (23051813030960592087418142364443/500000000000000000000000000000)
  cells := [(59,84),(59,85),(59,86),(59,87),(99,57),(130,64)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 51

theorem band204_checked : band204.check rectangle=true := by decide +kernel
#print axioms band204_checked

def band205 : Band CellKey where
  qlo := (131/264)
  qhi := (197/396)
  mlo := (1155837563451776649746192893401/50000000000000000000000000000)
  mhi := (23051813030960592087418142364443/500000000000000000000000000000)
  cells := [(80,79),(80,80),(99,57),(130,64)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 51

theorem band205_checked : band205.check rectangle=true := by decide +kernel
#print axioms band205_checked

def band206 : Band CellKey where
  qlo := (131/264)
  qhi := (197/396)
  mlo := (28142131979695431472081218274111/1000000000000000000000000000000)
  mhi := (23051813030960592087418142364443/500000000000000000000000000000)
  cells := [(99,57),(130,64)]
  lowerOrder := 99
  orderCap := 129
  rank := 28
  parentStrip := 51

theorem band206_checked : band206.check rectangle=true := by decide +kernel
#print axioms band206_checked

def band207 : Band CellKey where
  qlo := (131/264)
  qhi := (197/396)
  mlo := (36182741116751269035532994923857/1000000000000000000000000000000)
  mhi := (23051813030960592087418142364443/500000000000000000000000000000)
  cells := [(130,64)]
  lowerOrder := 130
  orderCap := 169
  rank := 36
  parentStrip := 51

theorem band207_checked : band207.check rectangle=true := by decide +kernel
#print axioms band207_checked

end ForestUnimodality.IntermediateBridgeCoverData

