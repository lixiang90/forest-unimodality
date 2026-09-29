import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell227
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 41
  A := (-29836161205571847364836913/100000000000000000000000000)
  B := (50800750380084386259582629/1000000000000000000000000000)
  C := (2419087714711861958338801/20000000000000000000000000)
  dδ := (36350263387347557519913011/1000000000000000000000000000)
  dM := (28142230807775788815894291/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(36508442147996600368742293/10000000000000000000000000), (57388942099750250847023381/10000000000000000000000000), (70101608696023651745576899/10000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/90)
  hi := (107/180)
  vmin := (7811/32400)
  damping := (7811/32400)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell227
