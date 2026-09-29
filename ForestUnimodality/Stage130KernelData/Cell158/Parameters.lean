import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-16452232311557072785745959/10000000000000000000000000)
  B := (11294968528145460373579567/100000000000000000000000000)
  C := (49964399296203217820666609/10000000000000000000000000000)
  dδ := (35127901097849911771220377/500000000000000000000000000)
  dM := (13480450732894755892787853/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12934529305355438211222463/2000000000000000000000000), (69142344751841537942027571/10000000000000000000000000), (60908028278784080100649589/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31833/60208)
  hi := (23881/45156)
  vmin := (508068275/2039064336)
  damping := (508068275/2039064336)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell158
