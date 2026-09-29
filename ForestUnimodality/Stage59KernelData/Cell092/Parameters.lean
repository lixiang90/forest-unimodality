import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell092
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 18
  density := (277865261123287868271521379491 / 1000000000000000000000000000000)
  probabilityCap := (1 / 2)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (60, 17), (60, 18), (61, 17), (61, 18), (62, 18), (63, 18), (64, 18)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (395 / 397)
def activityUpper : ℚ := (1)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (23)
  A := (398378860883145686486273 / 125000000000000000000000)
  B := (-4388934665992504091658333 / 50000000000000000000000000)
  C := (2471713059866362249827887 / 250000000000000000000000000)
  dδ := (1327236857387648349959619 / 10000000000000000000000000)
  dM := (0)
  wL := (0)
  wR := (17915685937 / 500000000000)
  wC := (1982084314063 / 2000000000000)
  price := ![(6394814833788522001611909 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (1985667746109109543795057 / 100000000000000000000000) else if j = 0 then (1626333498069152838638729 / 100000000000000000000000) else if j = 1 then (389266996630024166847761 / 20000000000000000000000) else if j = 2 then (997070872921267081778751 / 50000000000000000000000) else if j = 3 then (1207642982006988852106133 / 100000000000000000000000) else if j = 4 then (38119601637821971529263 / 2500000000000000000000) else if j = 5 then (9329554180557368070481061 / 1000000000000000000000000) else if j = 6 then (1466925654032184844766107 / 100000000000000000000000) else if j = 7 then (1434687414854999509827849 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (3294522650231926269950211 / 125000000000000000000000000000) else if j = 0 then (47307368637284920449418017 / 1000000000000000000000000000000) else if j = 1 then (85251984074559420464666823 / 1000000000000000000000000000000) else if j = 2 then (27549668834823609452344003 / 200000000000000000000000000000) else if j = 3 then (8953642371317673072011801 / 50000000000000000000000000000) else if j = 4 then (185960264635059363803322021 / 1000000000000000000000000000000) else if j = 5 then (185960264635059363803322021 / 1000000000000000000000000000000) else if j = 6 then (156688741498059278760206517 / 1000000000000000000000000000000) else if j = 7 then (21637969064017709924028519 / 200000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (395 / 792)
  hi := (1 / 2)
  vmin := (156815 / 627264)
  damping := (156815 / 627264)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell092
