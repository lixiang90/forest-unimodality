import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 123
  A := (5925497526855608654727803/50000000000000000000000000)
  B := (47459569162691790655816959/500000000000000000000000000)
  C := (2794327981203887922845297/4000000000000000000000000)
  dδ := (1503525994701820633903111/10000000000000000000000000)
  dM := (3293403660961940430246253/2000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(4380939685473267952708909/625000000000000000000000), (39376844683485989762061763/10000000000000000000000000), (13494456198747450059727271/500000000000000000000000), (19352352917693565359513741/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28/53)
  hi := (95449/180624)
  vmin := (8129868575/32625029376)
  damping := (8129868575/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell133
