import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 57
  A := (35124055259519788464217527/100000000000000000000000000)
  B := (21768055719687023213948507/500000000000000000000000000)
  C := (666133814775093924254179/200000000000000000000000000000000000000)
  dδ := (83934440061610465777519607/1000000000000000000000000000)
  dM := (83934475985547986678914079/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(54370226834864965326232777/10000000000000000000000000), (39419422891177307022303467/10000000000000000000000000), (2993021946245585152013291/62500000000000000000000)]
  retention := ![(4/5), (1/2), (1/20)]
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
end ForestUnimodality.Stage99KernelData.Cell059
