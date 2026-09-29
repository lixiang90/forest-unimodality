import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 86
  A := (-14695590884165489653412351/10000000000000000000000000)
  B := (19213244314662328293685789/200000000000000000000000000)
  C := (-7299210796991100706071487/5000000000000000000000000000)
  dδ := (6437856360089844187655217/100000000000000000000000000)
  dM := (2636495748937139286388609/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(3599026503181833813727053/500000000000000000000000), (6965699871396818565472131/1000000000000000000000000), (17575944828097259886590109/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24/49)
  hi := (9529/19404)
  vmin := (600/2401)
  damping := (600/2401)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell056
