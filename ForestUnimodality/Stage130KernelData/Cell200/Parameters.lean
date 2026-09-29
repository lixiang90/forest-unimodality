import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell200
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 70
  A := (-19955989910965372013862407/10000000000000000000000000)
  B := (13584880667393739450687917/100000000000000000000000000)
  C := (6811970211818323605798553/1250000000000000000000000000)
  dδ := (36340450438609665784195357/500000000000000000000000000)
  dM := (8534805877029958548485311/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7887752782866888523471971/500000000000000000000000), (52161674118546464740120427/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (12116/22791)
  hi := (24257/45582)
  vmin := (517280525/2077718724)
  damping := (517280525/2077718724)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell200
