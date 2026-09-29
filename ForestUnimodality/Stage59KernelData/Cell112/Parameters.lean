import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell112
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (70247917686709070062629310199 / 250000000000000000000000000000)
  probabilityCap := (3493 / 6868)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 22), (76, 22), (77, 22), (78, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (5227 / 5075)
def activityUpper : ℚ := (3493 / 3375)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (2808845146578450590055809 / 10000000000000000000000000)
  B := (7842269220417905084552501 / 100000000000000000000000000)
  C := (4399761291722340539323 / 40000000000000000000000)
  dδ := (681011585374946964988041 / 5000000000000000000000000)
  dM := (1209884998490605998236469 / 500000000000000000000000000)
  wL := (447506364169 / 250000000000)
  wR := (5524936358309 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(35102733314919185025893 / 7812500000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2493600268662893526538937 / 100000000000000000000000) else if j = 0 then (23729236439875265318733 / 1000000000000000000000) else if j = 1 then (1611723839589267370797643 / 50000000000000000000000) else if j = 2 then (3730994908286156430676783 / 100000000000000000000000) else if j = 3 then (1342688281876387890179103 / 100000000000000000000000) else if j = 4 then (228300484882280940723831 / 20000000000000000000000) else if j = 5 then (518567743395517410931461 / 50000000000000000000000) else if j = 6 then (2762355524635628611918037 / 500000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13415384737283470256959209 / 500000000000000000000000000000) else if j = 0 then (46423863326882124317890941 / 1000000000000000000000000000000) else if j = 1 then (41329423047663261930513501 / 500000000000000000000000000000) else if j = 2 then (130290104368563215710704059 / 1000000000000000000000000000000) else if j = 3 then (8182763139379775392652649 / 50000000000000000000000000000) else if j = 4 then (164208480934612528938200057 / 1000000000000000000000000000000) else if j = 5 then (164208480934612528938200057 / 1000000000000000000000000000000) else if j = 6 then (164208480934612528938200057 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (5227 / 10302)
  hi := (3493 / 6868)
  vmin := (11788875 / 47169424)
  damping := (11788875 / 47169424)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell112
