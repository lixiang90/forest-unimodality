import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 20
  A := (400691053250586851797177/3125000000000000000000000)
  B := (3000338155987031935056919/200000000000000000000000000)
  C := (-427339120991610671440597/20000000000000000000000000)
  dδ := (1564455511742336019098687/100000000000000000000000000)
  dM := (87744480950840926308451073/1000000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(72408675926556609336870451/100000000000000000000000000), (6338973291468293080885843/25000000000000000000000000), (2838840852200196773758023/625000000000000000000000)]
  retention := ![(3/5), (1/2), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37/140)
  hi := (19/70)
  vmin := (3811/19600)
  damping := (381100000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell002
