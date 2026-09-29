import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 119
  A := (2644438302845832339471599/25000000000000000000000000)
  B := (23331776579120423742441659/250000000000000000000000000)
  C := (67499517374605288999589447/100000000000000000000000000)
  dδ := (3662173913515413131714027/25000000000000000000000000)
  dM := (16081063330409929926223533/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(16381100378111534965341889/2500000000000000000000000), (41336918476466921745782201/10000000000000000000000000), (4705735326666842865961371/200000000000000000000000), (2108627748534266288515937/100000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95599/180624)
  hi := (11953/22578)
  vmin := (127000625/509766084)
  damping := (127000625/509766084)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell140
