import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 55
  A := (-23579685391717616404605451/50000000000000000000000000)
  B := (76150253742292922654044673/1000000000000000000000000000)
  C := (-5902184536730963743123013/25000000000000000000000000)
  dδ := (61495389624765757485835849/1000000000000000000000000000)
  dM := (1276612449516821437903169/1250000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(93333074669115745347625079/100000000000000000000000000), (3954641475273720896410623/1000000000000000000000000), (2303478577418263117948527/125000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22/51)
  hi := (67/153)
  vmin := (638/2601)
  damping := (638/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell024
