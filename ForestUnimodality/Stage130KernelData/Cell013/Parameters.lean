import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 30
  A := (1252691061078083499591429/6250000000000000000000000)
  B := (1687927070504224857927511/100000000000000000000000000)
  C := (-43701718247053593369155777/1000000000000000000000000000)
  dδ := (2341379367743583184147127/125000000000000000000000000)
  dM := (2426887109095130249866723/20000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(6633762901846116388782093/5000000000000000000000000), (47585687945776982132883859/5000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (89/255)
  hi := (91/255)
  vmin := (14774/65025)
  damping := (14774/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell013
