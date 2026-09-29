import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band176 : Band CellKey where
  qlo := (4631/9506)
  qhi := (9287/19012)
  mlo := (8700441477333907612792074943469/500000000000000000000000000000)
  mhi := (11038118994474807848391896995571/250000000000000000000000000000)
  cells := [(59,60),(59,61),(59,62),(99,49),(130,51),(130,52)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 44

theorem band176_checked : band176.check rectangle=true := by decide +kernel
#print axioms band176_checked

def band177 : Band CellKey where
  qlo := (4631/9506)
  qhi := (9287/19012)
  mlo := (22518789706040702056638311618391/1000000000000000000000000000000)
  mhi := (11038118994474807848391896995571/250000000000000000000000000000)
  cells := [(80,56),(80,57),(80,58),(80,59),(80,60),(80,61),(99,49),(130,51),(130,52)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 44

theorem band177_checked : band177.check rectangle=true := by decide +kernel
#print axioms band177_checked

def band178 : Band CellKey where
  qlo := (4631/9506)
  qhi := (9287/19012)
  mlo := (27636696457413588887692473349843/1000000000000000000000000000000)
  mhi := (11038118994474807848391896995571/250000000000000000000000000000)
  cells := [(99,49),(130,51),(130,52)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 44

theorem band178_checked : band178.check rectangle=true := by decide +kernel
#print axioms band178_checked

def band179 : Band CellKey where
  qlo := (4631/9506)
  qhi := (9287/19012)
  mlo := (16889092279530526542478733713793/500000000000000000000000000000)
  mhi := (11038118994474807848391896995571/250000000000000000000000000000)
  cells := [(130,51),(130,52)]
  lowerOrder := 130
  orderCap := 169
  rank := 33
  parentStrip := 44

theorem band179_checked : band179.check rectangle=true := by decide +kernel
#print axioms band179_checked

def band180 : Band CellKey where
  qlo := (9287/19012)
  qhi := (24/49)
  mlo := (8677083333333333333333333333333/500000000000000000000000000000)
  mhi := (11111570900536368041348121029389/250000000000000000000000000000)
  cells := [(59,63),(59,64),(59,65),(99,50),(130,53),(130,54)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 45

theorem band180_checked : band180.check rectangle=true := by decide +kernel
#print axioms band180_checked

def band181 : Band CellKey where
  qlo := (9287/19012)
  qhi := (24/49)
  mlo := (22458333333333333333333333333333/1000000000000000000000000000000)
  mhi := (11111570900536368041348121029389/250000000000000000000000000000)
  cells := [(80,62),(80,63),(80,64),(80,65),(99,50),(130,53),(130,54)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 45

theorem band181_checked : band181.check rectangle=true := by decide +kernel
#print axioms band181_checked

def band182 : Band CellKey where
  qlo := (9287/19012)
  qhi := (24/49)
  mlo := (441/16)
  mhi := (11111570900536368041348121029389/250000000000000000000000000000)
  cells := [(99,50),(130,53),(130,54)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 45

theorem band182_checked : band182.check rectangle=true := by decide +kernel
#print axioms band182_checked

def band183 : Band CellKey where
  qlo := (9287/19012)
  qhi := (24/49)
  mlo := (34708333333333333333333333333333/1000000000000000000000000000000)
  mhi := (11111570900536368041348121029389/250000000000000000000000000000)
  cells := [(130,53),(130,54)]
  lowerOrder := 130
  orderCap := 169
  rank := 34
  parentStrip := 45

theorem band183_checked : band183.check rectangle=true := by decide +kernel
#print axioms band183_checked

def band184 : Band CellKey where
  qlo := (24/49)
  qhi := (9529/19404)
  mlo := (17308636792947843425333193409591/1000000000000000000000000000000)
  mhi := (4473872973239584426487564277463/100000000000000000000000000000)
  cells := [(59,66),(59,67),(59,68),(99,51),(130,55),(130,56)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 46

theorem band184_checked : band184.check rectangle=true := by decide +kernel
#print axioms band184_checked

def band185 : Band CellKey where
  qlo := (24/49)
  qhi := (9529/19404)
  mlo := (11199706160142722216392066323853/500000000000000000000000000000)
  mhi := (4473872973239584426487564277463/100000000000000000000000000000)
  cells := [(80,66),(80,67),(80,68),(99,51),(130,55),(130,56)]
  lowerOrder := 80
  orderCap := 98
  rank := 22
  parentStrip := 46

theorem band185_checked : band185.check rectangle=true := by decide +kernel
#print axioms band185_checked

def band186 : Band CellKey where
  qlo := (24/49)
  qhi := (9529/19404)
  mlo := (13745093923811522720117535942911/500000000000000000000000000000)
  mhi := (4473872973239584426487564277463/100000000000000000000000000000)
  cells := [(99,51),(130,55),(130,56)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 46

theorem band186_checked : band186.check rectangle=true := by decide +kernel
#print axioms band186_checked

def band187 : Band CellKey where
  qlo := (24/49)
  qhi := (9529/19404)
  mlo := (34617273585895686850666386819183/1000000000000000000000000000000)
  mhi := (4473872973239584426487564277463/100000000000000000000000000000)
  cells := [(130,55),(130,56)]
  lowerOrder := 130
  orderCap := 169
  rank := 34
  parentStrip := 46

theorem band187_checked : band187.check rectangle=true := by decide +kernel
#print axioms band187_checked

def band188 : Band CellKey where
  qlo := (9529/19404)
  qhi := (4777/9702)
  mlo := (8631672597864768683274021352313/500000000000000000000000000000)
  mhi := (45019284153176910043101242918663/1000000000000000000000000000000)
  cells := [(59,69),(59,70),(59,71),(99,52),(130,57),(130,58)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 47

theorem band188_checked : band188.check rectangle=true := by decide +kernel
#print axioms band188_checked

def band189 : Band CellKey where
  qlo := (9529/19404)
  qhi := (4777/9702)
  mlo := (23356290558928197613564998953317/1000000000000000000000000000000)
  mhi := (45019284153176910043101242918663/1000000000000000000000000000000)
  cells := [(80,69),(80,70),(99,52),(130,57),(130,58)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 47

theorem band189_checked : band189.check rectangle=true := by decide +kernel
#print axioms band189_checked

def band190 : Band CellKey where
  qlo := (9529/19404)
  qhi := (4777/9702)
  mlo := (3427281766799246388947037889889/125000000000000000000000000000)
  mhi := (45019284153176910043101242918663/1000000000000000000000000000000)
  cells := [(99,52),(130,57),(130,58)]
  lowerOrder := 99
  orderCap := 129
  rank := 27
  parentStrip := 47

theorem band190_checked : band190.check rectangle=true := by decide +kernel
#print axioms band190_checked

def band191 : Band CellKey where
  qlo := (9529/19404)
  qhi := (4777/9702)
  mlo := (8631672597864768683274021352313/250000000000000000000000000000)
  mhi := (45019284153176910043101242918663/1000000000000000000000000000000)
  cells := [(130,57),(130,58)]
  lowerOrder := 130
  orderCap := 169
  rank := 34
  parentStrip := 47

theorem band191_checked : band191.check rectangle=true := by decide +kernel
#print axioms band191_checked

end ForestUnimodality.IntermediateBridgeCoverData

