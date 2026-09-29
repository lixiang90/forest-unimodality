import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (-12318067265275882038366717/10000000000000000000000000)
  B := (4026996954129881400863411/25000000000000000000000000)
  C := (-2879761918108532728344251/400000000000000000000000000)
  dδ := (11929782270415757727821671/100000000000000000000000000)
  dM := (32216458327070326451979643/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(49366267386295152874708947/10000000000000000000000000), (16359739058467003047780963/500000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (869/1824)
  hi := (581/1216)
  vmin := (829895/3326976)
  damping := (829895/3326976)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell040
