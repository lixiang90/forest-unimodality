import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 126
  A := (558641662205020579392567/4000000000000000000000000)
  B := (47871829350575718919902357/500000000000000000000000000)
  C := (17911509006319342729440791/25000000000000000000000000)
  dδ := (15353536509559925771206679/100000000000000000000000000)
  dM := (16707039403225402637853669/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(73537784435857638243305701/10000000000000000000000000), (38119108765046063602710547/10000000000000000000000000), (5841226945436716277981759/200000000000000000000000), (4600558073412181592232173/250000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23607/44732)
  hi := (94453/178928)
  vmin := (7978917175/32015229184)
  damping := (7978917175/32015229184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell129
