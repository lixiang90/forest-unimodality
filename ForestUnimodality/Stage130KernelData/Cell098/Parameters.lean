import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 90
  A := (-15774892816740208500903009/10000000000000000000000000)
  B := (96880960240999000609996017/1000000000000000000000000000)
  C := (14085687975162509717047543/5000000000000000000000000000)
  dδ := (61435365343501642521051309/1000000000000000000000000000)
  dM := (10261366794846497278032027/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(3103735456017803873152161/250000000000000000000000), (15189792133311581778798427/200000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/207)
  hi := (7427/14352)
  vmin := (51431975/205979904)
  damping := (51431975/205979904)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell098
