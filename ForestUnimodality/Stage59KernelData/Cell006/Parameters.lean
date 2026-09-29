import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell006
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 15
  upperRank := 24
  density := (1 / 4)
  probabilityCap := (19 / 63)

def pairs : List (ℕ × ℕ) := [(59, 15), (59, 16), (59, 17), (60, 15), (60, 16), (60, 17), (60, 18), (61, 16), (61, 17), (61, 18), (62, 16), (62, 17), (62, 18), (63, 16), (63, 17), (63, 18), (63, 19), (64, 16), (64, 17), (64, 18), (64, 19), (65, 17), (65, 18), (65, 19), (66, 17), (66, 18), (66, 19), (67, 17), (67, 18), (67, 19), (67, 20), (68, 17), (68, 18), (68, 19), (68, 20), (69, 18), (69, 19), (69, 20), (70, 18), (70, 19), (70, 20), (70, 21), (71, 18), (71, 19), (71, 20), (71, 21), (72, 18), (72, 19), (72, 20), (72, 21), (73, 19), (73, 20), (73, 21), (73, 22), (74, 19), (74, 20), (74, 21), (74, 22), (75, 19), (75, 20), (75, 21), (75, 22), (76, 19), (76, 20), (76, 21), (76, 22), (77, 20), (77, 21), (77, 22), (77, 23), (78, 20), (78, 21), (78, 22), (78, 23), (79, 20), (79, 21), (79, 22), (79, 23)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (37 / 89)
def activityUpper : ℚ := (19 / 44)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (46)
  A := (4164346639144777683654297 / 5000000000000000000000000)
  B := (743486954002338801261729 / 20000000000000000000000000)
  C := (-8058614075224183881385187 / 100000000000000000000000000)
  dδ := (5005300725328287736459743 / 100000000000000000000000000)
  dM := (0)
  wL := (4)
  wR := (0)
  wC := (0)
  price := ![(1174309738845584483168949 / 1250000000000000000000000), (7139657309577982502446503 / 1000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := {1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = 1 then (4811518957123247730578441 / 100000000000000000000000) else if j = 2 then (1494980041424475381006687 / 100000000000000000000000) else if j = 3 then (7719721403332213682801921 / 1000000000000000000000000) else if j = 4 then (3970386815941864711021481 / 1000000000000000000000000) else if j = 5 then (4142737869364988001485983 / 5000000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = 1 then (164579700793963206480718191 / 500000000000000000000000000000) else if j = 2 then (95282984670189224804626321 / 125000000000000000000000000000) else if j = 3 then (286851932796569666253927661 / 200000000000000000000000000000) else if j = 4 then (1107147810793777659225685709 / 500000000000000000000000000000) else if j = 5 then (2820313370653623089817009911 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (37 / 126)
  hi := (19 / 63)
  vmin := (3293 / 15876)
  damping := (32930000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell006
