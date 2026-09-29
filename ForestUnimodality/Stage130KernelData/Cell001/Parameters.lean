import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 19
  A := (2310037639276583321290559/20000000000000000000000000)
  B := (2890761374628065052960757/200000000000000000000000000)
  C := (-4921215214250536200413233/250000000000000000000000000)
  dδ := (15003096061276892034253017/1000000000000000000000000000)
  dM := (8253897183614312342125191/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(19914122371460181160074399/10000000000000000000000000), (31108402593281030412697419/10000000000000000000000000)]
  retention := ![(1/2), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9/35)
  hi := (37/140)
  vmin := (234/1225)
  damping := (374400000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell001
