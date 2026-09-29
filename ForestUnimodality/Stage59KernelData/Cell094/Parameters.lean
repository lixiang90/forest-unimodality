import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell094
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (277865261123287868271521379491 / 1000000000000000000000000000000)
  probabilityCap := (1 / 2)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 17), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 17), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 19), (67, 20), (67, 21), (67, 22), (68, 19), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 20), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 21), (74, 22), (75, 21), (75, 22), (76, 22), (77, 22), (78, 22), (79, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (395 / 397)
def activityUpper : ℚ := (1)

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (695335131372059191384949 / 250000000000000000000000)
  B := (-6531004031645533391969849 / 100000000000000000000000000)
  C := (851922891347103861114931 / 50000000000000000000000000)
  dδ := (1472888440409654553509 / 12500000000000000000000)
  dM := (0)
  wL := (0)
  wR := (29150492059 / 500000000000)
  wC := (1970849507941 / 2000000000000)
  price := ![(3366046224392019503568463 / 500000000000000000000000), (156793770593966277915321 / 625000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (2610297526219130404001589 / 100000000000000000000000) else if j = 0 then (1061260350164524091098883 / 50000000000000000000000) else if j = 1 then (1263016452273070022727097 / 50000000000000000000000) else if j = 2 then (439428770856695720681273 / 20000000000000000000000) else if j = 3 then (793998548457614994333653 / 50000000000000000000000) else if j = 4 then (470439652773136973706869 / 25000000000000000000000) else if j = 5 then (335103454207346551640967 / 25000000000000000000000) else if j = 6 then (350264685496401924069687 / 20000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (3294522650231926269950211 / 125000000000000000000000000000) else if j = 0 then (47307368637284920449418017 / 1000000000000000000000000000000) else if j = 1 then (85251984074559420464666823 / 1000000000000000000000000000000) else if j = 2 then (27549668834823609452344003 / 200000000000000000000000000000) else if j = 3 then (8953642371317673072011801 / 50000000000000000000000000000) else if j = 4 then (185960264635059363803322021 / 1000000000000000000000000000000) else if j = 5 then (185960264635059363803322021 / 1000000000000000000000000000000) else if j = 6 then (185960264635059363803322021 / 1000000000000000000000000000000) else 0

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
end ForestUnimodality.Stage59KernelData.Cell094
