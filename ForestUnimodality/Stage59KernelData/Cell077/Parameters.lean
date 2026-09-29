import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell077
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 19
  density := (17251153016544075690277703103 / 62500000000000000000000000000)
  probabilityCap := (49 / 99)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (60, 17), (60, 18), (60, 19), (61, 17), (61, 18), (61, 19), (62, 18), (62, 19), (63, 18), (63, 19), (64, 18), (64, 19), (65, 18), (65, 19), (66, 19), (67, 19), (68, 19)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (3193 / 3275)
def activityUpper : ℚ := (49 / 50)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (3029365222205606362649633 / 1000000000000000000000000)
  B := (-7744227220996967309130099 / 100000000000000000000000000)
  C := (-270471737629372288927443 / 25000000000000000000000000)
  dδ := (15630729252697147385609 / 125000000000000000000000)
  dM := (0)
  wL := (5090363620801 / 2500000000000)
  wR := (2454818189599 / 1250000000000)
  wC := (1 / 10000000000000)
  price := ![(6580148685501957750432211 / 1000000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5, 6, 7}
  fixedPrice := fun j => if j = -1 then (1109438266051312815818619 / 50000000000000000000000) else if j = 0 then (1704833406344798518716743 / 100000000000000000000000) else if j = 1 then (225158710267182833320021 / 10000000000000000000000) else if j = 2 then (191913858957431990859277 / 10000000000000000000000) else if j = 3 then (83916699922262272259843 / 6250000000000000000000) else if j = 4 then (882291868215906305294993 / 50000000000000000000000) else if j = 5 then (1333358028310513176961649 / 100000000000000000000000) else if j = 6 then (1643015071270567517558447 / 100000000000000000000000) else if j = 7 then (1652830858976929562231817 / 100000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (807404209768817755918701 / 31250000000000000000000000000) else if j = 0 then (1892871842070167797390521 / 40000000000000000000000000000) else if j = 1 then (43266858166241311086588127 / 500000000000000000000000000000) else if j = 2 then (5675128138729350665203631 / 40000000000000000000000000000) else if j = 3 then (94102890055461171744447963 / 500000000000000000000000000000) else if j = 4 then (199433126491165748594983909 / 1000000000000000000000000000000) else if j = 5 then (199433126491165748594983909 / 1000000000000000000000000000000) else if j = 6 then (199433126491165748594983909 / 1000000000000000000000000000000) else if j = 7 then (171470280713303884373994101 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (3193 / 6468)
  hi := (49 / 99)
  vmin := (10457075 / 41835024)
  damping := (10457075 / 41835024)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell077
