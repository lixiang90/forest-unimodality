import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell105
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (139834119030299925755241366451 / 500000000000000000000000000000)
  probabilityCap := (51 / 101)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 19), (66, 19), (67, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (407 / 401)
def activityUpper : ℚ := (51 / 50)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (24)
  A := (-1263707505981009975414509 / 1000000000000000000000000)
  B := (194208345918653518813457 / 1000000000000000000000000)
  C := (9338840853868228542022933 / 100000000000000000000000000)
  dδ := (1257508442166967999042981 / 10000000000000000000000000)
  dM := (2419716777758359593092363 / 500000000000000000000000000)
  wL := (1183774895201 / 2500000000000)
  wR := (408994817181 / 500000000000)
  wC := (3385625509447 / 5000000000000)
  price := ![(9627653608600262868932873 / 10000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6}
  fixedPrice := fun j => if j = -1 then (29435470965818337774067 / 1250000000000000000000) else if j = 0 then (713345643705432230774477 / 25000000000000000000000) else if j = 1 then (171044358428801018590093 / 4000000000000000000000) else if j = 2 then (6092963167669892499134221 / 100000000000000000000000) else if j = 3 then (60501832913076974307387 / 4000000000000000000000) else if j = 4 then (185097193428731827680167 / 10000000000000000000000) else if j = 5 then (492123576723840017166367 / 25000000000000000000000) else if j = 6 then (264456114808282585215693 / 10000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (13215405883269206343341959 / 500000000000000000000000000000) else if j = 0 then (5800338011532882890392131 / 125000000000000000000000000000) else if j = 1 then (3353327549467553037212101 / 40000000000000000000000000000) else if j = 2 then (16691697026294209427865171 / 125000000000000000000000000000) else if j = 3 then (170189852032803703970389979 / 1000000000000000000000000000000) else if j = 4 then (8663510567280731536954241 / 50000000000000000000000000000) else if j = 5 then (8663510567280731536954241 / 50000000000000000000000000000) else if j = 6 then (8663510567280731536954241 / 50000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (407 / 808)
  hi := (51 / 101)
  vmin := (2550 / 10201)
  damping := (2550 / 10201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell105
