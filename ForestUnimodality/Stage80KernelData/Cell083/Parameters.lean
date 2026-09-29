import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 35
  A := (10327496538847212076461801/5000000000000000000000000)
  B := (-24010243715454408081066973/1000000000000000000000000000)
  C := (16975949441977828290397297/5000000000000000000000000000000000000000)
  dδ := (11318439022114359926440841/100000000000000000000000000)
  dM := (2476478065381228915731171/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1971983571458973405476911/312500000000000000000000), (15320988744439835826938179/500000000000000000000000)]
  retention := ![(4/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (395/792)
  hi := (1/2)
  vmin := (156815/627264)
  damping := (156815/627264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell083
