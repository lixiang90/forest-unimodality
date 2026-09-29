import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell428.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch250_299
import ForestUnimodality.BinomialMassData.Q9_35.Batch250_299

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel250
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217058403186071245273/50000000000000000000)
  centralHi := (434116806372142490547/100000000000000000000)
  directionLo := (6796736896083765141/1562500000000000000)
  directionHi := (17399646453974438761/4000000000000000000)

def endpointA : IntegerEndpointWitness 250 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree250.table
  base := (8697848002905779714174552967823259163427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18531771368429656339504862670000000000000)
      constant := (581830548548149024069000618280323259163427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 250 interval.damping) (curvature.centralUpper 250 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree250.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 250 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree250.table
  base := (1739569600581134885441984146672160010009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-934269411900229301039255678580000000000000)
      constant := (30154630993996156361101007913934679202452205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 250 interval.damping) (curvature.centralUpper 250 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree250.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 250 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel251
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6796736896083765141/1562500000000000000)
  centralHi := (17399646453974438761/4000000000000000000)
  directionLo := (435863762349410416613/100000000000000000000)
  directionHi := (217931881174705208307/50000000000000000000)

def endpointA : IntegerEndpointWitness 251 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree251.table
  base := (8917395942484589569730254400368436910289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18606664553707302454943483835000000000000)
      constant := (586692400977994953773862363025993436910289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 251 interval.damping) (curvature.centralUpper 251 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree251.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 251 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree251.table
  base := (8917395942484497232402535413273066249477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-938044028438222665257362185296000000000000)
      constant := (30406114856793319645650725472891580246224373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 251 interval.damping) (curvature.centralUpper 251 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree251.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 251 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel252
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435863762349410416613/100000000000000000000)
  centralHi := (217931881174705208307/50000000000000000000)
  directionLo := (436734619885693118087/100000000000000000000)
  directionHi := (54591827485711639761/12500000000000000000)

def endpointA : IntegerEndpointWitness 252 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree252.table
  base := (142786936905505844781938350742775385337/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18681557738984948570382105000000000000000)
      constant := (591574396784049269648341861677537624661568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 252 interval.damping) (curvature.centralUpper 252 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree252.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 252 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree252.table
  base := (913836396195229308680720947284231646683/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-67272760355444002105390620858000000000000)
      constant := (2189902779941874350233422747982148107633905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 252 interval.damping) (curvature.centralUpper 252 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree252.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 252 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel253
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436734619885693118087/100000000000000000000)
  centralHi := (54591827485711639761/12500000000000000000)
  directionLo := (218801872183499830781/50000000000000000000)
  directionHi := (437603744366999661563/100000000000000000000)

def endpointA : IntegerEndpointWitness 253 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree253.table
  base := (2340188013168404153150207777737361796443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18756450924262594685820726165000000000000)
      constant := (596476535957676455101923992236574447185772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 253 interval.damping) (curvature.centralUpper 253 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree253.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 253 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree253.table
  base := (9360752052673545595360265335711234557751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-945593261514209393693575198728000000000000)
      constant := (30912203180751779830594466709268650493329799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 253 interval.damping) (curvature.centralUpper 253 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree253.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 253 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel254
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218801872183499830781/50000000000000000000)
  centralHi := (437603744366999661563/100000000000000000000)
  directionLo := (438471146098960451669/100000000000000000000)
  directionHi := (43847114609896045167/10000000000000000000)

def endpointA : IntegerEndpointWitness 254 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree254.table
  base := (9584560206096137527984889951025753993931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18831344109540240801259347330000000000000)
      constant := (601398818490324330453193060263525753993931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 254 interval.damping) (curvature.centralUpper 254 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree254.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 254 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree254.table
  base := (2396140051524018812028742121291082939057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-237341969513050689477920426361000000000000)
      constant := (7791701910267719907910745048532063064013793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 254 interval.damping) (curvature.centralUpper 254 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree254.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 254 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel255
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438471146098960451669/100000000000000000000)
  centralHi := (43847114609896045167/10000000000000000000)
  directionLo := (878673670570942861/200000000000000000)
  directionHi := (439336835285471430501/100000000000000000000)

def endpointA : IntegerEndpointWitness 255 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree255.table
  base := (2452447103437493387549208126501963060947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18906237294817886916697968495000000000000)
      constant := (606341244373522932440149667296632852243788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 255 interval.damping) (curvature.centralUpper 255 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree255.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 255 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree255.table
  base := (980978841374991893349848497156955298911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-476571247295098061064894106080000000000000)
      constant := (15711226149864256056973195031398454048233195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 255 interval.damping) (curvature.centralUpper 255 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree255.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 255 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel256
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (878673670570942861/200000000000000000)
  centralHi := (439336835285471430501/100000000000000000000)
  directionLo := (440200822030094564299/100000000000000000000)
  directionHi := (4402008220300945643/1000000000000000000)

def endpointA : IntegerEndpointWitness 256 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree256.table
  base := (5018218333623138311293542915974097908007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-18981130480095533032136589660000000000000)
      constant := (611303813598883413006144240391948195816014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 256 interval.damping) (curvature.centralUpper 256 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree256.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 256 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree256.table
  base := (2007287333449245745365082042252912813957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-956917111128189486347894718876000000000000)
      constant := (31679137156313623729195111490675163639419465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 256 interval.damping) (curvature.centralUpper 256 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree256.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 256 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel257
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440200822030094564299/100000000000000000000)
  centralHi := (4402008220300945643/1000000000000000000)
  directionLo := (55132889542179204951/12500000000000000000)
  directionHi := (441063116337433639609/100000000000000000000)

def endpointA : IntegerEndpointWitness 257 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree257.table
  base := (2052900991655246310407910084255472336459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3811204733074635829515042165000000000000)
      constant := (123257305231619391391612136008380472336459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 257 interval.damping) (curvature.centralUpper 257 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree257.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 257 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree257.table
  base := (40095722493266365432599153903636243397/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-240172931916545712641500306398000000000000)
      constant := (7984215552604770634649744199580503259292992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 257 interval.damping) (curvature.centralUpper 257 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree257.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 257 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel258
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/12500000000000000000)
  centralHi := (441063116337433639609/100000000000000000000)
  directionLo := (441923728114485898847/100000000000000000000)
  directionHi := (13810116503577684339/3125000000000000000)

def endpointA : IntegerEndpointWitness 258 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree258.table
  base := (327937289956562254563263904700862142541/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19130916850650825263013831990000000000000)
      constant := (621289382042933718103369204922927588561312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 258 interval.damping) (curvature.centralUpper 258 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree258.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 258 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree258.table
  base := (10493993278609955314282538596023456673557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-964466344204176214784107732308000000000000)
      constant := (32195627461641626083700168554689949377004293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 258 interval.damping) (curvature.centralUpper 258 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree258.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 258 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel259
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441923728114485898847/100000000000000000000)
  centralHi := (13810116503577684339/3125000000000000000)
  directionLo := (1729619793640507937/390625000000000000)
  directionHi := (442782667171970031873/100000000000000000000)

def endpointA : IntegerEndpointWitness 259 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree259.table
  base := (5362450810047817722374398890969004394977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19205810035928471378452453155000000000000)
      constant := (626312381245241773482276843397563008789954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 259 interval.damping) (curvature.centralUpper 259 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree259.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 259 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree259.table
  base := (335153175627987598335287120319773637257/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (26)
      previous := (9)
      next := (0)
      square := (262126148471761404035174077500000000000)
      linear := (-34580034312220342107221937108000000000000)
      constant := (1159122603913636076565500358934807323686392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 259 interval.damping) (curvature.centralUpper 259 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree259.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 259 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel260
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1729619793640507937/390625000000000000)
  centralHi := (442782667171970031873/100000000000000000000)
  directionLo := (443639943225631027071/100000000000000000000)
  directionHi := (3465937056450242399/781250000000000000)

def endpointA : IntegerEndpointWitness 260 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree260.table
  base := (547861498732906683701281765555477962499/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-3856140644241223498778214864000000000000)
      constant := (126271104751389219064119324372221911849996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 260 interval.damping) (curvature.centralUpper 260 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree260.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 260 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree260.table
  base := (5478614987329052676022290934131889401467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-486007788640081471610160372870000000000000)
      constant := (16358139276921979180947252284692462580671883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 260 interval.damping) (curvature.centralUpper 260 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree260.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 260 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel261
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443639943225631027071/100000000000000000000)
  centralHi := (3465937056450242399/781250000000000000)
  directionLo := (444495565897522372927/100000000000000000000)
  directionHi := (6945243217148787077/1562500000000000000)

def endpointA : IntegerEndpointWitness 261 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree261.table
  base := (11190978334298343553591263232287031248479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19355596406483763609329695485000000000000)
      constant := (636418809570047540338064846007912031248479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 261 interval.damping) (curvature.centralUpper 261 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree261.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 261 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree261.table
  base := (11190978334298318718514296476316876648933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-975790193818156307438427252456000000000000)
      constant := (32978164394036112720507645327804726955797717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 261 interval.damping) (curvature.centralUpper 261 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree261.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 261 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel262
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444495565897522372927/100000000000000000000)
  centralHi := (6945243217148787077/1562500000000000000)
  directionLo := (44534954471726608873/10000000000000000000)
  directionHi := (445349544717266088731/100000000000000000000)

def endpointA : IntegerEndpointWitness 262 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree262.table
  base := (11426146691092012604471236848182546810453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19430489591761409724768316650000000000000)
      constant := (641502238676621856055707071140682546810453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 262 interval.damping) (curvature.centralUpper 262 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree262.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 262 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree262.table
  base := (11426146691091990827293794896425914878201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-979564810356149671656533759172000000000000)
      constant := (33241090429769984851150050023313669829031849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 262 interval.damping) (curvature.centralUpper 262 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree262.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 262 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel263
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44534954471726608873/10000000000000000000)
  centralHi := (445349544717266088731/100000000000000000000)
  directionLo := (89240377824658210237/20000000000000000000)
  directionHi := (223100944561645525593/50000000000000000000)

def endpointA : IntegerEndpointWitness 263 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree263.table
  base := (5831367518594401053792003417093869301711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19505382777039055840206937815000000000000)
      constant := (646605811068818703754441747934812738603422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 263 interval.damping) (curvature.centralUpper 263 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree263.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 263 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree263.table
  base := (1457841879648597876505662319512866700187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-245834856723535758968660066472000000000000)
      constant := (8376264165165227039792791876464960936618326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 263 interval.damping) (curvature.centralUpper 263 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree263.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 263 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel264
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89240377824658210237/20000000000000000000)
  centralHi := (223100944561645525593/50000000000000000000)
  directionLo := (447052608464050072107/100000000000000000000)
  directionHi := (111763152116012518027/25000000000000000000)

def endpointA : IntegerEndpointWitness 264 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree264.table
  base := (11900743364811326374154708551400175772689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19580275962316701955645558980000000000000)
      constant := (651729526738860697745494011751400175772689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 264 interval.damping) (curvature.centralUpper 264 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree264.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 264 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree264.table
  base := (5950371682405654815129058133963012441729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-493557021716068200046373386302000000000000)
      constant := (16885031543163895374043986953629787609644721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 264 interval.damping) (curvature.centralUpper 264 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree264.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 264 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel265
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447052608464050072107/100000000000000000000)
  centralHi := (111763152116012518027/25000000000000000000)
  directionLo := (223950855999608085589/50000000000000000000)
  directionHi := (447901711999216171179/100000000000000000000)

def endpointA : IntegerEndpointWitness 265 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree265.table
  base := (12140171666254207996672634145878563091969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19655169147594348071084180145000000000000)
      constant := (656873385679042460621353154736503563091969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 265 interval.damping) (curvature.centralUpper 265 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree265.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 265 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree265.table
  base := (12140171666254193315001489356856080672041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-990888659970129764310853279320000000000000)
      constant := (34036109706393069126920862052435947952930009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 265 interval.damping) (curvature.centralUpper 265 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree265.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 265 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel266
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223950855999608085589/50000000000000000000)
  centralHi := (447901711999216171179/100000000000000000000)
  directionLo := (448749208900858476759/100000000000000000000)
  directionHi := (11218730222521461919/2500000000000000000)

def endpointA : IntegerEndpointWitness 266 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree266.table
  base := (6190509966941574378493303709719779639547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19730062332871994186522801310000000000000)
      constant := (662037387881729694163868000691939559279094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 266 interval.damping) (curvature.centralUpper 266 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree266.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 266 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree266.table
  base := (6190509966941567941858896032396182889669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-71047376893437366323497127574000000000000)
      constant := (2450228322891618763194607734231573280227683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 266 interval.damping) (curvature.centralUpper 266 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree266.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 266 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel267
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448749208900858476759/100000000000000000000)
  centralHi := (11218730222521461919/2500000000000000000)
  directionLo := (7024923566478096519/1562500000000000000)
  directionHi := (449595108254598177217/100000000000000000000)

def endpointA : IntegerEndpointWitness 267 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree267.table
  base := (12623288160134015875900160851749343677311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19804955518149640301961422475000000000000)
      constant := (667221533339358265593842082097374343677311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 267 interval.damping) (curvature.centralUpper 267 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree267.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 267 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree267.table
  base := (12623288160134004588429939089519493344571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-998437893046116492747066292752000000000000)
      constant := (34571323528225928916848035407869255173883979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 267 interval.damping) (curvature.centralUpper 267 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree267.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 267 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel268
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7024923566478096519/1562500000000000000)
  centralHi := (449595108254598177217/100000000000000000000)
  directionLo := (225219709530372467419/50000000000000000000)
  directionHi := (450439419060744934839/100000000000000000000)

def endpointA : IntegerEndpointWitness 268 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree268.table
  base := (6433488168755971648027516214416111472737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19879848703427286417400043640000000000000)
      constant := (672425822044433308853917136938832222945474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 268 interval.damping) (curvature.centralUpper 268 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree268.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 268 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree268.table
  base := (64334881687559666995810036556347970327/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-250553127396027464241293199867000000000000)
      constant := (8710122682313904846955655801362252527301150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 268 interval.damping) (curvature.centralUpper 268 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree268.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 268 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel269
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225219709530372467419/50000000000000000000)
  centralHi := (450439419060744934839/100000000000000000000)
  directionLo := (14102567194856692639/3125000000000000000)
  directionHi := (451282150235414164449/100000000000000000000)

def endpointA : IntegerEndpointWitness 269 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree269.table
  base := (13112084458590447697216386520222015298311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-19954741888704932532838664805000000000000)
      constant := (677650253989528340623858329585847015298311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 269 interval.damping) (curvature.centralUpper 269 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree269.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 269 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree269.table
  base := (6556042229295219509847840584834203295461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-502993563061051610591639653092000000000000)
      constant := (17555349061603918208066787104761475961477589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 269 interval.damping) (curvature.centralUpper 269 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree269.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 269 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel270
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14102567194856692639/3125000000000000000)
  centralHi := (451282150235414164449/100000000000000000000)
  directionLo := (452123310611625569043/100000000000000000000)
  directionHi := (113030827652906392261/25000000000000000000)

def endpointA : IntegerEndpointWitness 270 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree270.table
  base := (2671722503202111790027846296817095499123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4005927014796515729655457194000000000000)
      constant := (136578965833456878154884133679317095499123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 270 interval.damping) (curvature.centralUpper 270 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree270.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 270 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree270.table
  base := (2671722503202110268370014492904060216921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1009761742660096585401385812900000000000000)
      constant := (35381945709721990466480024898281494753145645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 270 interval.damping) (curvature.centralUpper 270 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree270.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 270 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel271
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452123310611625569043/100000000000000000000)
  centralHi := (113030827652906392261/25000000000000000000)
  directionLo := (113240727235095828831/25000000000000000000)
  directionHi := (18118516357615332613/4000000000000000000)

def endpointA : IntegerEndpointWitness 271 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree271.table
  base := (13606560502479964722086448422055303694999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-20104528259260224763715907135000000000000)
      constant := (688159547570409146972867034472680303694999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 271 interval.damping) (curvature.centralUpper 271 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree271.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 271 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree271.table
  base := (2721312100495991610272483567180540627823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1013536359198089949619492319616000000000000)
      constant := (35654233488440758235463099867088432453816635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 271 interval.damping) (curvature.centralUpper 271 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree271.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 271 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel272
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113240727235095828831/25000000000000000000)
  centralHi := (18118516357615332613/4000000000000000000)
  directionLo := (113450238472934555699/25000000000000000000)
  directionHi := (453800953891738222797/100000000000000000000)

def endpointA : IntegerEndpointWitness 272 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree272.table
  base := (13855928410772168953801721726557511978979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-20179421444537870879154528300000000000000)
      constant := (693444409191676113159941112206557511978979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 272 interval.damping) (curvature.centralUpper 272 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree272.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 272 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree272.table
  base := (13855928410772163105179165161364145868859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1017310975736083313837598826332000000000000)
      constant := (35927561459010041416973175061943643147574091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 272 interval.damping) (curvature.centralUpper 272 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree272.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 272 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel273
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113450238472934555699/25000000000000000000)
  centralHi := (453800953891738222797/100000000000000000000)
  directionLo := (227318727027916165559/50000000000000000000)
  directionHi := (454637454055832331119/100000000000000000000)

def endpointA : IntegerEndpointWitness 273 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree273.table
  base := (2821343246745132786845508925714816575689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4050862925963103398918629893000000000000)
      constant := (139749882804784756324917078965839816575689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 273 interval.damping) (curvature.centralUpper 273 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree273.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 273 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree273.table
  base := (22041744115196341885082938542672500683/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (26)
      previous := (9)
      next := (0)
      square := (262126148471761404035174077500000000000)
      linear := (-36467342581217024216275190466000000000000)
      constant := (1292926057895675933352312000997893200764960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 273 interval.damping) (curvature.centralUpper 273 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree273.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 273 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel274
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227318727027916165559/50000000000000000000)
  centralHi := (454637454055832331119/100000000000000000000)
  directionLo := (18218896717757048069/4000000000000000000)
  directionHi := (227736208971963100863/50000000000000000000)

def endpointA : IntegerEndpointWitness 274 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree274.table
  base := (14358923964243115705655778697681585614937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-20329207815093163110031770630000000000000)
      constant := (704074562060054818409091743910181585614937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 274 interval.damping) (curvature.centralUpper 274 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree274.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 274 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree274.table
  base := (14358923964243111209938645538772544851249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1024860208812070042273811839764000000000000)
      constant := (36477337974299643022820752343147054697711201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 274 interval.damping) (curvature.centralUpper 274 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree274.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 274 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel275
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18218896717757048069/4000000000000000000)
  centralHi := (227736208971963100863/50000000000000000000)
  directionLo := (11407646349735232531/2500000000000000000)
  directionHi := (456305853989409301241/100000000000000000000)

def endpointA : IntegerEndpointWitness 275 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree275.table
  base := (1826568949411320317268769437014487645399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-20404101000370809225470391795000000000000)
      constant := (709419853293035261783523891011740901163192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 275 interval.damping) (curvature.centralUpper 275 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree275.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 275 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree275.table
  base := (7306275797645279298314666577582728700551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-514317412675031703245959173240000000000000)
      constant := (18376893259163763979804952101576553706326999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 275 interval.damping) (curvature.centralUpper 275 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree275.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 275 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel276
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11407646349735232531/2500000000000000000)
  centralHi := (456305853989409301241/100000000000000000000)
  directionLo := (28571110659299612873/6250000000000000000)
  directionHi := (457137770548793805969/100000000000000000000)

def endpointA : IntegerEndpointWitness 276 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree276.table
  base := (371689977997415655452728303365598004663/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4095798837129691068181802592000000000000)
      constant := (142957057543178746706856058648924784037304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 276 interval.damping) (curvature.centralUpper 276 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree276.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 276 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree276.table
  base := (14867599119896622762508866562436492650359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1032409441888056770710024853196000000000000)
      constant := (37031275252820983412235394037210588139867591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 276 interval.damping) (curvature.centralUpper 276 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree276.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 276 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel277
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28571110659299612873/6250000000000000000)
  centralHi := (457137770548793805969/100000000000000000000)
  directionLo := (91593635180538431753/20000000000000000000)
  directionHi := (228984087951346079383/50000000000000000000)

def endpointA : IntegerEndpointWitness 277 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree277.table
  base := (3024813306230347180341881225643869030727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4110777474185220291269526825000000000000)
      constant := (144034173064344132563507529624768869030727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 277 interval.damping) (curvature.centralUpper 277 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree277.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 277 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree277.table
  base := (3024813306230346574431999487487819228887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1036184058426050134928131359912000000000000)
      constant := (37309804177441440409761776677485315711077315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 277 interval.damping) (curvature.centralUpper 277 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree277.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 277 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel278
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91593635180538431753/20000000000000000000)
  centralHi := (228984087951346079383/50000000000000000000)
  directionLo := (229398539128389350873/50000000000000000000)
  directionHi := (458797078256778701747/100000000000000000000)

def endpointA : IntegerEndpointWitness 278 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree278.table
  base := (615278152888294571585807509086638625993/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4125756111240749514357251058000000000000)
      constant := (145115317220733504466798033179933193129965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 278 interval.damping) (curvature.centralUpper 278 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree278.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 278 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree278.table
  base := (15381953822207361633648743918967582633051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1039958674964043499146237866628000000000000)
      constant := (37589373291853321114884287012778211549019499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 278 interval.damping) (curvature.centralUpper 278 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree278.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 278 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel279
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229398539128389350873/50000000000000000000)
  centralHi := (458797078256778701747/100000000000000000000)
  directionLo := (229812242871367850381/50000000000000000000)
  directionHi := (459624485742735700763/100000000000000000000)

def endpointA : IntegerEndpointWitness 279 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree279.table
  base := (15641260986275275885178238705408374043969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-20703673741481393687224876455000000000000)
      constant := (731002450054946076586899608346033374043969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 279 interval.damping) (curvature.centralUpper 279 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree279.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 279 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree279.table
  base := (7820630493137636778350793702308631624611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-521866645751018431682172186672000000000000)
      constant := (18934991297862000994289761315785722949605939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 279 interval.damping) (curvature.centralUpper 279 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree279.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 279 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel280
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229812242871367850381/50000000000000000000)
  centralHi := (459624485742735700763/100000000000000000000)
  directionLo := (23022520320959203507/5000000000000000000)
  directionHi := (460450406419184070141/100000000000000000000)

def endpointA : IntegerEndpointWitness 280 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree280.table
  base := (15901988016626787102872964138906971144417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-20778566926759039802663497620000000000000)
      constant := (736448457168827641990830380538906971144417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 280 interval.damping) (curvature.centralUpper 280 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree280.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 280 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree280.table
  base := (15901988016626785061552100514412095189441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-149643986862861461083207268580000000000000)
      constant := (5450233155531968219348418370320884666326087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 280 interval.damping) (curvature.centralUpper 280 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree280.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 280 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel281
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23022520320959203507/5000000000000000000)
  centralHi := (460450406419184070141/100000000000000000000)
  directionLo := (57659356034074887381/12500000000000000000)
  directionHi := (461274848272599099049/100000000000000000000)

def endpointA : IntegerEndpointWitness 281 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree281.table
  base := (404103372664800950017583799890148730441/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4170692022407337183620423757000000000000)
      constant := (148382921487728471720751294089246189843528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 281 interval.damping) (curvature.centralUpper 281 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree281.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 281 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree281.table
  base := (3232826981318407242229143736030260673627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1051282524578023591800557386776000000000000)
      constant := (38434321770525824618546831230960613865038615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 281 interval.damping) (curvature.centralUpper 281 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree281.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 281 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel282
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57659356034074887381/12500000000000000000)
  centralHi := (461274848272599099049/100000000000000000000)
  directionLo := (462097819218211473823/100000000000000000000)
  directionHi := (14440556850569108557/3125000000000000000)

def endpointA : IntegerEndpointWitness 282 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree282.table
  base := (16427701649559275413318767447570566030847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-20928353297314332033540739950000000000000)
      constant := (747400900857778473260327243240070566030847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 282 interval.damping) (curvature.centralUpper 282 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree282.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 282 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree282.table
  base := (4106925412389818461122836178807154127789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-263764285279004239004665973373000000000000)
      constant := (9679512910201541833253666696392750552261661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 282 interval.damping) (curvature.centralUpper 282 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree282.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 282 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel283
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462097819218211473823/100000000000000000000)
  centralHi := (14440556850569108557/3125000000000000000)
  directionLo := (462919327100893883819/100000000000000000000)
  directionHi := (23145966355044694191/5000000000000000000)

def endpointA : IntegerEndpointWitness 283 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree283.table
  base := (3338537647794829453854663513412033138807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4200649296518395629795872223000000000000)
      constant := (150581467483936326777819361198537033138807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 283 interval.damping) (curvature.centralUpper 283 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree283.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 283 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree283.table
  base := (3338537647794829178793195619392161828563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1058831757654010320236770400208000000000000)
      constant := (39002821699243642427528908230465879647997935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 283 interval.damping) (curvature.centralUpper 283 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree283.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 283 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel284
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462919327100893883819/100000000000000000000)
  centralHi := (23145966355044694191/5000000000000000000)
  directionLo := (92747875939206698339/20000000000000000000)
  directionHi := (28983711231002093231/6250000000000000000)

def endpointA : IntegerEndpointWitness 284 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree284.table
  base := (8479547334169503939939599078423540393313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21078139667869624264417982280000000000000)
      constant := (758433917117854194801377354506847080786626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 284 interval.damping) (curvature.centralUpper 284 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree284.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 284 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree284.table
  base := (529971708385593958569814865603584442927/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-265651593548000921113719226731000000000000)
      constant := (9822157986379966315877028488117405101627384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 284 interval.damping) (curvature.centralUpper 284 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree284.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 284 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel285
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92747875939206698339/20000000000000000000)
  centralHi := (28983711231002093231/6250000000000000000)
  directionLo := (3716463877683124341/800000000000000000)
  directionHi := (232278992355195271313/50000000000000000000)

def endpointA : IntegerEndpointWitness 285 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree285.table
  base := (1722692093121223399209585206915512557883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-4230606570629454075971320689000000000000)
      constant := (152796127989170906548825666326956025115766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 285 interval.damping) (curvature.centralUpper 285 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree285.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 285 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree285.table
  base := (689076837248489317407784377205362328451/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1066380990729997048672983413640000000000000)
      constant := (39575482379319196301697333575066568852352475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 285 interval.damping) (curvature.centralUpper 285 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree285.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 285 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel286
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3716463877683124341/800000000000000000)
  centralHi := (232278992355195271313/50000000000000000000)
  directionLo := (465375149782943380639/100000000000000000000)
  directionHi := (2908594686143396129/625000000000000000)

def endpointA : IntegerEndpointWitness 286 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree286.table
  base := (17496167021207551402491870957190953643147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21227926038424916495295224610000000000000)
      constant := (769547505897296373513918329029690953643147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 286 interval.damping) (curvature.centralUpper 286 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree286.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 286 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree286.table
  base := (2187020877650943809499218675729511636561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-267538901816997603222772480089000000000000)
      constant := (9965843250082177026563682358490292140382978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 286 interval.damping) (curvature.centralUpper 286 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree286.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 286 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel287
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465375149782943380639/100000000000000000000)
  centralHi := (2908594686143396129/625000000000000000)
  directionLo := (116547720621430033543/25000000000000000000)
  directionHi := (466190882485720134173/100000000000000000000)

def endpointA : IntegerEndpointWitness 287 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree287.table
  base := (2220854116499171491725248509358616534691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21302819223702562610733845775000000000000)
      constant := (775134514965848128933482079945493932277528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 287 interval.damping) (curvature.centralUpper 287 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree287.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 287 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree287.table
  base := (888341646599668556081319732463844667591/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (26)
      previous := (9)
      next := (0)
      square := (262126148471761404035174077500000000000)
      linear := (-38354650850213706325328443824000000000000)
      constant := (1434010850294219744878751842188334563365685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 287 interval.damping) (curvature.centralUpper 287 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree287.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 287 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel288
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116547720621430033543/25000000000000000000)
  centralHi := (466190882485720134173/100000000000000000000)
  directionLo := (467005190324617326979/100000000000000000000)
  directionHi := (23350259516230866349/5000000000000000000)

def endpointA : IntegerEndpointWitness 288 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree288.table
  base := (18038918657292140580019316527319729469211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21377712408980208726172466940000000000000)
      constant := (780741667145232243996812697487319729469211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 288 interval.damping) (curvature.centralUpper 288 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree288.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 288 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree288.table
  base := (1127432416080758741754217047683692559129/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-269426210085994285331825733447000000000000)
      constant := (10110568700684982589387767867381203741589284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 288 interval.damping) (curvature.centralUpper 288 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree288.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 288 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel289
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467005190324617326979/100000000000000000000)
  centralHi := (23350259516230866349/5000000000000000000)
  directionLo := (233909040370102832371/50000000000000000000)
  directionHi := (467818080740205664743/100000000000000000000)

def endpointA : IntegerEndpointWitness 289 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree289.table
  base := (2289053023859961578776026980874687063863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21452605594257854841611088105000000000000)
      constant := (786368962429224553992974541187622496510904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 289 interval.damping) (curvature.centralUpper 289 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree289.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 289 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree289.table
  base := (9156212095439846003059532171164871496159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-540739728440985252772704720252000000000000)
      constant := (20366642991764528269171045523947678703311791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 289 interval.damping) (curvature.centralUpper 289 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree289.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 289 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel290
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233909040370102832371/50000000000000000000)
  centralHi := (467818080740205664743/100000000000000000000)
  directionLo := (468629561108523242083/100000000000000000000)
  directionHi := (117157390277130810521/25000000000000000000)

def endpointA : IntegerEndpointWitness 290 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree290.table
  base := (18587349526584620585421863363911504312483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21527498779535500957049709270000000000000)
      constant := (792016400811653651423020788376411504312483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 290 interval.damping) (curvature.centralUpper 290 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree290.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 290 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree290.table
  base := (18587349526584620038358018877272214630241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1085254073419963869763515947220000000000000)
      constant := (41025337350303132431604375941386338516881809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 290 interval.damping) (curvature.centralUpper 290 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree290.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 290 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel291
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468629561108523242083/100000000000000000000)
  centralHi := (117157390277130810521/25000000000000000000)
  directionLo := (469439638741856409171/100000000000000000000)
  directionHi := (117359909685464102293/25000000000000000000)

def endpointA : IntegerEndpointWitness 291 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree291.table
  base := (18863694658287650687148175186194691088321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21602391964813147072488330435000000000000)
      constant := (797683982286400262528439355161819691088321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 291 interval.damping) (curvature.centralUpper 291 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree291.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 291 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree291.table
  base := (2357961832285956275951028094876248183399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-272257172489489308495405613484000000000000)
      constant := (10329607225690578405809074170292172321973102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 291 interval.damping) (curvature.centralUpper 291 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree291.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 291 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel292
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469439638741856409171/100000000000000000000)
  centralHi := (117359909685464102293/25000000000000000000)
  directionLo := (470248320889508531773/100000000000000000000)
  directionHi := (235124160444754265887/50000000000000000000)

def endpointA : IntegerEndpointWitness 292 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree292.table
  base := (9570729789960514439843029729528261955267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21677285150090793187926951600000000000000)
      constant := (803371706847396633253529149689056523910534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 292 interval.damping) (curvature.centralUpper 292 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree292.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 292 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree292.table
  base := (2392682447490128557417496284625758020691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-273200826623987649549932240163000000000000)
      constant := (10403140160152320041141474348356524286027718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 292 interval.damping) (curvature.centralUpper 292 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree292.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 292 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel293
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470248320889508531773/100000000000000000000)
  centralHi := (235124160444754265887/50000000000000000000)
  directionLo := (235527807369278436683/50000000000000000000)
  directionHi := (471055614738556873367/100000000000000000000)

def endpointA : IntegerEndpointWitness 293 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree293.table
  base := (4855161071366979008175898322189705906277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21752178335368439303365572765000000000000)
      constant := (809079574488625924467958249064383823625108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 293 interval.damping) (curvature.centralUpper 293 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree293.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 293 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree293.table
  base := (19420644285467915664248385423789517106869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-1096577923033943962417835467368000000000000)
      constant := (41907732563549206938257239447792486338236581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 293 interval.damping) (curvature.centralUpper 293 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree293.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 293 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel294
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235527807369278436683/50000000000000000000)
  centralHi := (471055614738556873367/100000000000000000000)
  directionLo := (29491345463412363929/6250000000000000000)
  directionHi := (94372305482919564573/20000000000000000000)

def endpointA : IntegerEndpointWitness 294 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree294.table
  base := (615664024030056007937969227825134206757/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21827071520646085418804193930000000000000)
      constant := (814807585204121616279540891902904294616224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 294 interval.damping) (curvature.centralUpper 294 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree294.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 294 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree294.table
  base := (19701248768961791931048205959591723334309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-157193219938848189519420282012000000000000)
      constant := (6029134953041390638519620699502742063340163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 294 interval.damping) (curvature.centralUpper 294 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree294.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 294 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel295
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29491345463412363929/6250000000000000000)
  centralHi := (94372305482919564573/20000000000000000000)
  directionLo := (94533213196496137303/20000000000000000000)
  directionHi := (118166516495620171629/25000000000000000000)

def endpointA : IntegerEndpointWitness 295 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree295.table
  base := (39029830125948965090324183587358630417/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21901964705923731534242815095000000000000)
      constant := (820555738987966921270902734737352618773504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 295 interval.damping) (curvature.centralUpper 295 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree295.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 295 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree295.table
  base := (1998327302448586984315461453425947462613/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-552063578054965345427024240400000000000000)
      constant := (21250598481770470087646778844724357128340185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 295 interval.damping) (curvature.centralUpper 295 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree295.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 295 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel296
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94533213196496137303/20000000000000000000)
  centralHi := (118166516495620171629/25000000000000000000)
  directionLo := (473469237447030257763/100000000000000000000)
  directionHi := (118367309361757564441/25000000000000000000)

def endpointA : IntegerEndpointWitness 296 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree296.table
  base := (20266717046172516704698551912970132059421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-21976857891201377649681436260000000000000)
      constant := (826324035834294206497345836072970132059421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 296 interval.damping) (curvature.centralUpper 296 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree296.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 296 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree296.table
  base := (10133358523086258228280945774405806178083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-553950886323962027536077493758000000000000)
      constant := (21399744720007655020484798783115484502726067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 296 interval.damping) (curvature.centralUpper 296 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree296.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 296 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel297
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473469237447030257763/100000000000000000000)
  centralHi := (118367309361757564441/25000000000000000000)
  directionLo := (474271048753758374089/100000000000000000000)
  directionHi := (47427104875375837409/10000000000000000000)

def endpointA : IntegerEndpointWitness 297 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree297.table
  base := (10275790414101342058576274483325540347871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22051751076479023765120057425000000000000)
      constant := (832112475737284424086650019837276080695742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 297 interval.damping) (curvature.centralUpper 297 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree297.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 297 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree297.table
  base := (10275790414101341949828381681564074757803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-555838194592958709645130747116000000000000)
      constant := (21549411050213855360478207059250039663132347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 297 interval.damping) (curvature.centralUpper 297 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree297.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 297 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel298
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474271048753758374089/100000000000000000000)
  centralHi := (47427104875375837409/10000000000000000000)
  directionLo := (47507150678956466531/10000000000000000000)
  directionHi := (475071506789564665311/100000000000000000000)

def endpointA : IntegerEndpointWitness 298 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree298.table
  base := (10418932182402674304896133611014234092391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22126644261756669880558678590000000000000)
      constant := (837921058691166550284999580094528468184782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 298 interval.damping) (curvature.centralUpper 298 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree298.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 298 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree298.table
  base := (5209466091201337104788904148492188243287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-278862751430977695877092000237000000000000)
      constant := (10849798736123840512835777572619317223921063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 298 interval.damping) (curvature.centralUpper 298 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree298.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 298 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel299
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47507150678956466531/10000000000000000000)
  centralHi := (475071506789564665311/100000000000000000000)
  directionLo := (475870618383426693333/100000000000000000000)
  directionHi := (237935309191713346667/50000000000000000000)

def endpointA : IntegerEndpointWitness 299 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree299.table
  base := (10562783825128478943380034088656034446217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-22201537447034315995997299755000000000000)
      constant := (843749784690217032796536878342937068892434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 299 interval.damping) (curvature.centralUpper 299 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree299.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 299 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree299.table
  base := (5281391912564239429916827817818738142917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-279806405565476036931618626916000000000000)
      constant := (10925151992984452492413880055907418169002933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 299 interval.damping) (curvature.centralUpper 299 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree299.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 299 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel299
