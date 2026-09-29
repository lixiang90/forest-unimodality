import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell093
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (277865261123287868271521379491 / 1000000000000000000000000000000)
  probabilityCap := (1 / 2)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (395 / 397)
def activityUpper : ℚ := (1)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (3107442982766585843791063 / 1000000000000000000000000)
  B := (-8055368403086668460666431 / 100000000000000000000000000)
  C := (1479999011793779566115159 / 100000000000000000000000000)
  dδ := (641142983767334639910729 / 5000000000000000000000000)
  dM := (0)
  wL := (0)
  wR := (131994985523 / 2500000000000)
  wC := (9868005014477 / 10000000000000)
  price := ![(6772344835350408764895747 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (2253699079039127894930061 / 100000000000000000000000) else if j = 0 then (1816895883508453479748823 / 100000000000000000000000) else if j = 1 then (87513934313683250820759 / 4000000000000000000000) else if j = 2 then (118673415669535953220759 / 6250000000000000000000) else if j = 3 then (1356678602811251721504959 / 100000000000000000000000) else if j = 4 then (163706452152678956224463 / 10000000000000000000000) else if j = 5 then (8134610448163116791509 / 781250000000000000000) else if j = 6 then (1426987622960677626338111 / 100000000000000000000000) else if j = 7 then (5396882953912655267458831 / 1000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (3294522650231926269950211 / 125000000000000000000000000000) else if j = 0 then (47307368637284920449418017 / 1000000000000000000000000000000) else if j = 1 then (85251984074559420464666823 / 1000000000000000000000000000000) else if j = 2 then (27549668834823609452344003 / 200000000000000000000000000000) else if j = 3 then (8953642371317673072011801 / 50000000000000000000000000000) else if j = 4 then (185960264635059363803322021 / 1000000000000000000000000000000) else if j = 5 then (185960264635059363803322021 / 1000000000000000000000000000000) else if j = 6 then (185960264635059363803322021 / 1000000000000000000000000000000) else if j = 7 then (156688741498059278760206517 / 1000000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell093
