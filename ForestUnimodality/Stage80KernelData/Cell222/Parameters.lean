import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell222
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 25
  A := (17946052968679649486460903/10000000000000000000000000)
  B := (8409582633421053970979031/500000000000000000000000000)
  C := (8373958679808499172558811/50000000000000000000000000)
  dδ := (34386680733127283904337901/500000000000000000000000000)
  dM := (40711811022214937447888383/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(348090800020546531357013/200000000000000000000000), (4734930826525361458045893/2500000000000000000000000), (856253262562879785546599/312500000000000000000000), (24463319274845587436573169/5000000000000000000000000)]
  retention := ![(19/20), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (63/103)
  hi := (129/209)
  vmin := (10320/43681)
  damping := (10320/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell222
