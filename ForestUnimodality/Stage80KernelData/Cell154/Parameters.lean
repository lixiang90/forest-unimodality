import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (8889068146373705292973/50000000000000000000000)
  B := (67797813797906655852720803/1000000000000000000000000000)
  C := (72449247281411435425702017/10000000000000000000000000000)
  dδ := (2988321903759214720475157/25000000000000000000000000)
  dM := (16359018131930551463032453/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(36472149297088254371601579/5000000000000000000000000), (26642792747514686624299429/1000000000000000000000000), (1025656160914584802412719/200000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23881/45156)
  hi := (95549/180624)
  vmin := (8128831175/32625029376)
  damping := (8128831175/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell154
