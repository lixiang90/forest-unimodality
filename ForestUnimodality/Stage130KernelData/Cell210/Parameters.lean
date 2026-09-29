import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell210
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-8590629731617964398537879/5000000000000000000000000)
  B := (10366249984144566831378853/100000000000000000000000000)
  C := (1130682694690150931482453/250000000000000000000000000)
  dδ := (61710029258323702283650647/1000000000000000000000000000)
  dM := (2218710042426808200233257/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11690989732060545591707523/1000000000000000000000000), (10890172695339515041013101/10000000000000000000000000), (8323155602622092530396003/125000000000000000000000), (68594449326255917398498241/10000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97103/182328)
  hi := (57/107)
  vmin := (2850/11449)
  damping := (2850/11449)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell210
