import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band384 : Band CellKey where
  qlo := (31833/60208)
  qhi := (23881/45156)
  mlo := (4254470080817386206607763493991/250000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(59,173),(99,136),(130,157),(130,158),(130,159)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 90

theorem band384_checked : band384.check rectangle=true := by decide +kernel
#print axioms band384_checked

def band385 : Band CellKey where
  qlo := (31833/60208)
  qhi := (23881/45156)
  mlo := (4538101419538545287048281060257/200000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(80,153),(99,136),(130,157),(130,158),(130,159)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 90

theorem band385_checked : band385.check rectangle=true := by decide +kernel
#print axioms band385_checked

def band386 : Band CellKey where
  qlo := (31833/60208)
  qhi := (23881/45156)
  mlo := (685442401909467777731250785143/25000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(99,136),(130,157),(130,158),(130,159)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 90

theorem band386_checked : band386.check rectangle=true := by decide +kernel
#print axioms band386_checked

def band387 : Band CellKey where
  qlo := (31833/60208)
  qhi := (23881/45156)
  mlo := (6996239688455257317532766634563/200000000000000000000000000000)
  mhi := (11415764701173436222568165100187/250000000000000000000000000000)
  cells := [(130,157),(130,158),(130,159)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 90

theorem band387_checked : band387.check rectangle=true := by decide +kernel
#print axioms band387_checked

def band388 : Band CellKey where
  qlo := (23881/45156)
  qhi := (95549/180624)
  mlo := (17013427665386346272593119760541/1000000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(59,174),(99,137),(130,160),(130,161),(130,162)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 91

theorem band388_checked : band388.check rectangle=true := by decide +kernel
#print axioms band388_checked

def band389 : Band CellKey where
  qlo := (23881/45156)
  qhi := (95549/180624)
  mlo := (4536914044103025672691498602811/200000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(80,154),(99,137),(130,160),(130,161),(130,162)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 91

theorem band389_checked : band389.check rectangle=true := by decide +kernel
#print axioms band389_checked

def band390 : Band CellKey where
  qlo := (23881/45156)
  qhi := (95549/180624)
  mlo := (548210446995782268783556081173/20000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(99,137),(130,160),(130,161),(130,162)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 91

theorem band390_checked : band390.check rectangle=true := by decide +kernel
#print axioms band390_checked

def band391 : Band CellKey where
  qlo := (23881/45156)
  qhi := (95549/180624)
  mlo := (17486022878313744780165150865001/500000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(130,160),(130,161),(130,162)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 91

theorem band391_checked : band391.check rectangle=true := by decide +kernel
#print axioms band391_checked

def band392 : Band CellKey where
  qlo := (95549/180624)
  qhi := (15929/30104)
  mlo := (17008977336932638583715236361353/1000000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(59,175),(99,138),(130,163),(130,164),(130,165)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 91

theorem band392_checked : band392.check rectangle=true := by decide +kernel
#print axioms band392_checked

def band393 : Band CellKey where
  qlo := (95549/180624)
  qhi := (15929/30104)
  mlo := (22678636449243518111620315148471/1000000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(80,155),(99,138),(130,163),(130,164),(130,165)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 91

theorem band393_checked : band393.check rectangle=true := by decide +kernel
#print axioms band393_checked

def band394 : Band CellKey where
  qlo := (95549/180624)
  qhi := (15929/30104)
  mlo := (3425419047021156381442651767217/125000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(99,138),(130,163),(130,164),(130,165)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 91

theorem band394_checked : band394.check rectangle=true := by decide +kernel
#print axioms band394_checked

def band395 : Band CellKey where
  qlo := (95549/180624)
  qhi := (15929/30104)
  mlo := (34962897859250423755414652520559/1000000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(130,163),(130,164),(130,165)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 91

theorem band395_checked : band395.check rectangle=true := by decide +kernel
#print axioms band395_checked

def band396 : Band CellKey where
  qlo := (15929/30104)
  qhi := (95599/180624)
  mlo := (17004529336080921348549671021663/1000000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(59,176),(99,139),(130,166),(130,167),(130,168)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 91

theorem band396_checked : band396.check rectangle=true := by decide +kernel
#print axioms band396_checked

def band397 : Band CellKey where
  qlo := (15929/30104)
  qhi := (95599/180624)
  mlo := (22672705781441228464732894695551/1000000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(80,156),(99,139),(130,166),(130,167),(130,168)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 91

theorem band397_checked : band397.check rectangle=true := by decide +kernel
#print axioms band397_checked

def band398 : Band CellKey where
  qlo := (15929/30104)
  qhi := (95599/180624)
  mlo := (27396186152574817728218914423791/1000000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(99,139),(130,166),(130,167),(130,168)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 91

theorem band398_checked : band398.check rectangle=true := by decide +kernel
#print axioms band398_checked

def band399 : Band CellKey where
  qlo := (15929/30104)
  qhi := (95599/180624)
  mlo := (17476877373194280274898272994487/500000000000000000000000000000)
  mhi := (45639201208552414760621022023893/1000000000000000000000000000000)
  cells := [(130,166),(130,167),(130,168)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 91

theorem band399_checked : band399.check rectangle=true := by decide +kernel
#print axioms band399_checked

end ForestUnimodality.IntermediateBridgeCoverData

