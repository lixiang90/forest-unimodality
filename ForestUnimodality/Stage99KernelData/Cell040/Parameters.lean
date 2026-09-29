import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 49
  A := (-3008220765698894463824331/2500000000000000000000000)
  B := (12882832312623793136197037/100000000000000000000000000)
  C := (-13879365983584857936750101/2500000000000000000000000000)
  dδ := (97420802183913038363449743/1000000000000000000000000000)
  dM := (1330681166452085141798517/625000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9885523733577046279208389/1250000000000000000000000), (19898216825534159823973823/500000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (581/1216)
  hi := (23/48)
  vmin := (368935/1478656)
  damping := (368935/1478656)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell040
