import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell349.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch200_249
import ForestUnimodality.BinomialMassData.Q9_35.Batch200_249

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel200
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96973565247465633293/25000000000000000000)
  centralHi := (387894260989862533173/100000000000000000000)
  directionLo := (194436279141901090253/50000000000000000000)
  directionHi := (388872558283802180507/100000000000000000000)

def endpointA : IntegerEndpointWitness 200 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree200.table
  base := (-192568587913266071070759963463842017569/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-53420252681918271725480806760000000000000)
      constant := (1305694214174993214280305500338314110875584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 200 interval.damping) (curvature.centralUpper 200 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree200.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 200 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree200.table
  base := (-616219481339026195555789421866090215103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3366700058888107137226863848050000000000000)
      constant := (84715692429380602626862079812214039486498825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 200 interval.damping) (curvature.centralUpper 200 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree200.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 200 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel201
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194436279141901090253/50000000000000000000)
  centralHi := (388872558283802180507/100000000000000000000)
  directionLo := (6091381259638094593/1562500000000000000)
  directionHi := (389848400616838053953/100000000000000000000)

def endpointA : IntegerEndpointWitness 201 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree201.table
  base := (-743045737808961158043509455905520563153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-53690851487977165994169848000000000000000)
      constant := (1319518760017735794015094318550511670989552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 201 interval.damping) (curvature.centralUpper 201 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree201.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 201 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree201.table
  base := (-1486091475654296520314555235676281450377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3383747783669817476154273446170000000000000)
      constant := (85610291193564894728898507440632622089315270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 201 interval.damping) (curvature.centralUpper 201 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree201.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 201 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel202
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6091381259638094593/1562500000000000000)
  centralHi := (389848400616838053953/100000000000000000000)
  directionLo := (390821806378334255877/100000000000000000000)
  directionHi := (195410903189167127939/50000000000000000000)

def endpointA : IntegerEndpointWitness 202 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree202.table
  base := (-89441011347862193037956787379042030629/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-53961450294036060262858889240000000000000)
      constant := (1333415580092904465117060593215482620079488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 202 interval.damping) (curvature.centralUpper 202 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree202.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 202 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree202.table
  base := (-2862112363195448772773336310738766638467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3400795508451527815081683044290000000000000)
      constant := (86509556910925359469110652230185002173575585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 202 interval.damping) (curvature.centralUpper 202 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree202.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 202 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel203
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390821806378334255877/100000000000000000000)
  centralHi := (195410903189167127939/50000000000000000000)
  directionLo := (391792793729213099901/100000000000000000000)
  directionHi := (195896396864606549951/50000000000000000000)

def endpointA : IntegerEndpointWitness 203 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree203.table
  base := (-171930353616121256232157355276187215311/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-54232049100094954531547930480000000000000)
      constant := (1347384674338265442276361843727324018220096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 203 interval.damping) (curvature.centralUpper 203 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree203.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 203 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree203.table
  base := (-2750885657913993914082573529967386775509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-69751902719045676612430462090000000000000)
      constant := (1783948766890820701861839422444163066122455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 203 interval.damping) (curvature.centralUpper 203 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree203.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 203 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel204
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391792793729213099901/100000000000000000000)
  centralHi := (195896396864606549951/50000000000000000000)
  directionLo := (392761380605908422889/100000000000000000000)
  directionHi := (39276138060590842289/10000000000000000000)

def endpointA : IntegerEndpointWitness 204 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree204.table
  base := (-1319251425393728141421867799672308623123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-54502647906153848800236971720000000000000)
      constant := (1361426042692328477960318084842621531015016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 204 interval.damping) (curvature.centralUpper 204 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree204.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 204 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree204.table
  base := (-2638502850836658086680138376144802376873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3434890958014948492936502240530000000000000)
      constant := (88322089189973214237836733368828523417666115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 204 interval.damping) (curvature.centralUpper 204 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree204.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 204 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel205
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392761380605908422889/100000000000000000000)
  centralHi := (39276138060590842289/10000000000000000000)
  directionLo := (78745516944846273657/20000000000000000000)
  directionHi := (196863792362115684143/50000000000000000000)

def endpointA : IntegerEndpointWitness 205 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree205.table
  base := (-2524963957109908683065404043120239163571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-54773246712212743068926012960000000000000)
      constant := (1375539685094334492343076784152519043345716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 205 interval.damping) (curvature.centralUpper 205 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree205.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 205 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree205.table
  base := (-2524963957153095085595479167515628377169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3451938682796658831863911838650000000000000)
      constant := (89235355744172893829148242399408671047593595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 205 interval.damping) (curvature.centralUpper 205 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree205.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 205 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel206
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78745516944846273657/20000000000000000000)
  centralHi := (196863792362115684143/50000000000000000000)
  directionLo := (394691423583150997753/100000000000000000000)
  directionHi := (197345711791575498877/50000000000000000000)

def endpointA : IntegerEndpointWitness 206 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree206.table
  base := (-2410268991835301759676310734143437566613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-55043845518271637337615054200000000000000)
      constant := (1389725601484243467587450790783426249733548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 206 interval.damping) (curvature.centralUpper 206 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree206.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 206 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree206.table
  base := (-602567247968301837881697989770239570279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3468986407578369170791321436770000000000000)
      constant := (90153289236571827067193600758029165221126580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 206 interval.damping) (curvature.centralUpper 206 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree206.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 206 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel207
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394691423583150997753/100000000000000000000)
  centralHi := (197345711791575498877/50000000000000000000)
  directionLo := (98913228617123003377/25000000000000000000)
  directionHi := (395652914468492013509/100000000000000000000)

def endpointA : IntegerEndpointWitness 207 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree207.table
  base := (-2294417969796836573113317967882939266729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-55314444324330531606304095440000000000000)
      constant := (1403983791802722599451692655553468242933084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 207 interval.damping) (curvature.centralUpper 207 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree207.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 207 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree207.table
  base := (-573604492457526587452181527627906274083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3486034132360079509718731034890000000000000)
      constant := (91075889663535901642965819351570651851398660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 207 interval.damping) (curvature.centralUpper 207 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree207.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 207 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel208
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98913228617123003377/25000000000000000000)
  centralHi := (395652914468492013509/100000000000000000000)
  directionLo := (79322414891310360349/20000000000000000000)
  directionHi := (198306037228275900873/50000000000000000000)

def endpointA : IntegerEndpointWitness 208 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree208.table
  base := (-2177410905653810249296473643202448322327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-55585043130389425874993136680000000000000)
      constant := (1418314255991134699432122186867190206710692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 208 interval.damping) (curvature.centralUpper 208 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree208.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 208 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree208.table
  base := (-2177410905683010524096390929706972244217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3503081857141789848646140633010000000000000)
      constant := (92003157021473609037769396399597791800166835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 208 interval.damping) (curvature.centralUpper 208 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree208.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 208 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel209
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79322414891310360349/20000000000000000000)
  centralHi := (198306037228275900873/50000000000000000000)
  directionLo := (397568920417638938271/100000000000000000000)
  directionHi := (12424028763051216821/3125000000000000000)

def endpointA : IntegerEndpointWitness 209 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree209.table
  base := (-2059247813894454450511754710243147221377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-55855641936448320143682177920000000000000)
      constant := (1432716993991526840879595476924027411114492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 209 interval.damping) (curvature.centralUpper 209 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree209.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 209 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree209.table
  base := (-2059247813920082439985647262562746411321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3520129581923500187573550231130000000000000)
      constant := (92935091306835349423033345994866127129226355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 209 interval.damping) (curvature.centralUpper 209 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree209.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 209 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel210
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (397568920417638938271/100000000000000000000)
  centralHi := (12424028763051216821/3125000000000000000)
  directionLo := (79704693803907046121/20000000000000000000)
  directionHi := (199261734509767615303/50000000000000000000)

def endpointA : IntegerEndpointWitness 210 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree210.table
  base := (-1939928708838714439233165457745218804853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-56126240742507214412371219160000000000000)
      constant := (1447192005746619242744216508569019124780588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 210 interval.damping) (curvature.centralUpper 210 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree210.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 210 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree210.table
  base := (-1939928708861206682743705162800819328277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-72187291973575725030631833250000000000000)
      constant := (1915748826859443899497289830085995903358615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 210 interval.damping) (curvature.centralUpper 210 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree210.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 210 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel211
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79704693803907046121/20000000000000000000)
  centralHi := (199261734509767615303/50000000000000000000)
  directionLo := (3195805893847066451/800000000000000000)
  directionHi := (49934467091360413297/12500000000000000000)

def endpointA : IntegerEndpointWitness 211 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree211.table
  base := (-1819453604640970269622501752949050285529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-56396839548566108681060260400000000000000)
      constant := (1461739291199794384809338098333203798857884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 211 interval.damping) (curvature.centralUpper 211 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree211.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 211 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree211.table
  base := (-454863401165177506087748523819364561473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3554225031486920865428369427370000000000000)
      constant := (94812960645838003935635758218751022729756460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 211 interval.damping) (curvature.centralUpper 211 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree211.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 211 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel212
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3195805893847066451/800000000000000000)
  centralHi := (49934467091360413297/12500000000000000000)
  directionLo := (200212869912250847859/50000000000000000000)
  directionHi := (400425739824501695719/100000000000000000000)

def endpointA : IntegerEndpointWitness 212 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree212.table
  base := (-1697822515292701592054620986659991586401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-56667438354625002949749301640000000000000)
      constant := (1476358850295086348473460816653360033654396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 212 interval.damping) (curvature.centralUpper 212 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree212.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 212 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree212.table
  base := (-339564503062005065605733146167156017899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3571272756268631204355779025490000000000000)
      constant := (95758895692583206952349833469121233878073725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 212 interval.damping) (curvature.centralUpper 212 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree212.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 212 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel213
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200212869912250847859/50000000000000000000)
  centralHi := (400425739824501695719/100000000000000000000)
  directionLo := (100343373595157323857/25000000000000000000)
  directionHi := (401373494380629295429/100000000000000000000)

def endpointA : IntegerEndpointWitness 213 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree213.table
  base := (-1575035454625097508801739788978603772743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-56938037160683897218438342880000000000000)
      constant := (1491050682977170377327495797009085584909028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 213 interval.damping) (curvature.centralUpper 213 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree213.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 213 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree213.table
  base := (-1575035454640300613290221091888766195869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3588320481050341543283188623610000000000000)
      constant := (96709497652959728860728619674833252282012095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 213 interval.damping) (curvature.centralUpper 213 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree213.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 213 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel214
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100343373595157323857/25000000000000000000)
  centralHi := (401373494380629295429/100000000000000000000)
  directionLo := (201159508145050522417/50000000000000000000)
  directionHi := (80463803258020208967/20000000000000000000)

def endpointA : IntegerEndpointWitness 214 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree214.table
  base := (-1451092436311612873719045798525212081423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-57208635966742791487127384120000000000000)
      constant := (1505814789191352651956022288845899151674308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 214 interval.damping) (curvature.centralUpper 214 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree214.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 214 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree214.table
  base := (-1451092436324954661091934385102135579631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3605368205832051882210598221730000000000000)
      constant := (97664766523617582059437829655253976782990405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 214 interval.damping) (curvature.centralUpper 214 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree214.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 214 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel215
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201159508145050522417/50000000000000000000)
  centralHi := (80463803258020208967/20000000000000000000)
  directionLo := (80652464251491317509/20000000000000000000)
  directionHi := (201631160628728293773/50000000000000000000)

def endpointA : IntegerEndpointWitness 215 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree215.table
  base := (-1325993473870472385466014729881388366959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-57479234772801685755816425360000000000000)
      constant := (1520651168883560273564402389305474446532164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 215 interval.damping) (curvature.centralUpper 215 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree215.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 215 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree215.table
  base := (-132599347388218049695548530368423091441/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3622415930613762221138007819850000000000000)
      constant := (98624702301244809257224651885547363425969550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 215 interval.damping) (curvature.centralUpper 215 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree215.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 215 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel216
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80652464251491317509/20000000000000000000)
  centralHi := (201631160628728293773/50000000000000000000)
  directionLo := (404203424803983639443/100000000000000000000)
  directionHi := (101050856200995909861/25000000000000000000)

def endpointA : IntegerEndpointWitness 216 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree216.table
  base := (-119973858066712378212358499445222313877/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-57749833578860580024505466600000000000000)
      constant := (1535559822000331451200312344742191107444920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 216 interval.damping) (curvature.centralUpper 216 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree216.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 216 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree216.table
  base := (-1199738580677398049674439985007283277471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3639463655395472560065417417970000000000000)
      constant := (99589304982566882571534662662057215597019605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 216 interval.damping) (curvature.centralUpper 216 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree216.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 216 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel217
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404203424803983639443/100000000000000000000)
  centralHi := (101050856200995909861/25000000000000000000)
  directionLo := (202571171135348865649/50000000000000000000)
  directionHi := (405142342270697731299/100000000000000000000)

def endpointA : IntegerEndpointWitness 217 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree217.table
  base := (-536163884958320702585495998124139020847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-58020432384919474293194507840000000000000)
      constant := (1550540748488805887497835213540006887833224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 217 interval.damping) (curvature.centralUpper 217 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree217.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 217 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree217.table
  base := (-67020485620353577785099080764293610629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-74622681228105773448833204410000000000000)
      constant := (2052215807435634995319718963332856511149680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 217 interval.damping) (curvature.centralUpper 217 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree217.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 217 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel218
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202571171135348865649/50000000000000000000)
  centralHi := (405142342270697731299/100000000000000000000)
  directionLo := (406079088821259944257/100000000000000000000)
  directionHi := (203039544410629972129/50000000000000000000)

def endpointA : IntegerEndpointWitness 218 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree218.table
  base := (-943761054686081362375825134643755211301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-58291031190978368561883549080000000000000)
      constant := (1565593948296715358025900638101424979154796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 218 interval.damping) (curvature.centralUpper 218 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree218.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 218 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree218.table
  base := (-943761054693992752875441496254183452589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3673559104958893237920236614210000000000000)
      constant := (101532511043381082360161014042933725054115695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 218 interval.damping) (curvature.centralUpper 218 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree218.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 218 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel219
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406079088821259944257/100000000000000000000)
  centralHi := (203039544410629972129/50000000000000000000)
  directionLo := (407013679444834208031/100000000000000000000)
  directionHi := (12719177482651069001/3125000000000000000)

def endpointA : IntegerEndpointWitness 219 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree219.table
  base := (-814038447896789482253455177764650305591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-58561629997037262830572590320000000000000)
      constant := (1580719421372374479470447135353941398777636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 219 interval.damping) (curvature.centralUpper 219 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree219.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 219 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree219.table
  base := (-407019223951865791563193181981753363479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3690606829740603576847646212330000000000000)
      constant := (102511114416506060222933974628042940851895290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 219 interval.damping) (curvature.centralUpper 219 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree219.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 219 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel220
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407013679444834208031/100000000000000000000)
  centralHi := (12719177482651069001/3125000000000000000)
  directionLo := (50993266119860710609/12500000000000000000)
  directionHi := (407946128958885684873/100000000000000000000)

def endpointA : IntegerEndpointWitness 220 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree220.table
  base := (-683159962326663217222357019661181776953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-58832228803096157099261631560000000000000)
      constant := (1595917167664671662021800805721355272892188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 220 interval.damping) (curvature.centralUpper 220 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree220.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 220 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree220.table
  base := (-170789990583188666319156448529058266143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3707654554522313915775055810450000000000000)
      constant := (103494384680590467531144370513441522899179860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 220 interval.damping) (curvature.centralUpper 220 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree220.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 220 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel221
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50993266119860710609/12500000000000000000)
  centralHi := (407946128958885684873/100000000000000000000)
  directionLo := (16355058080476868689/4000000000000000000)
  directionHi := (204438226005960858613/50000000000000000000)

def endpointA : IntegerEndpointWitness 221 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree221.table
  base := (-551125610612368618446713342750275803609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-59102827609155051367950672800000000000000)
      constant := (1611187187123060241475304918473998896785564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 221 interval.damping) (curvature.centralUpper 221 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree221.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 221 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree221.table
  base := (-551125610617713545454451280089790923909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3724702279304024254702465408570000000000000)
      constant := (104482321832538324655990770283252001223642295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 221 interval.damping) (curvature.centralUpper 221 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree221.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 221 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel222
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16355058080476868689/4000000000000000000)
  centralHi := (204438226005960858613/50000000000000000000)
  directionLo := (102451165771544193349/25000000000000000000)
  directionHi := (409804663086176773397/100000000000000000000)

def endpointA : IntegerEndpointWitness 222 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree222.table
  base := (-417935405251513472361308268283762850667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-59373426415213945636639714040000000000000)
      constant := (1626529479697549786685220337126864948597332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 222 interval.damping) (curvature.centralUpper 222 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree222.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 222 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree222.table
  base := (-6530240707128176194663157540866241189/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3741750004085734593629875006690000000000000)
      constant := (105474925869287720809537522018595217338156480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 222 interval.damping) (curvature.centralUpper 222 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree222.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 222 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel223
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102451165771544193349/25000000000000000000)
  centralHi := (409804663086176773397/100000000000000000000)
  directionLo := (51341347062530347921/12500000000000000000)
  directionHi := (410730776500242783369/100000000000000000000)

def endpointA : IntegerEndpointWitness 223 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree223.table
  base := (-283589358604777657206220790084806961041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-59644025221272839905328755280000000000000)
      constant := (1641944045338697578138586745704660772155836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 223 interval.damping) (curvature.centralUpper 223 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree223.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 223 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree223.table
  base := (-283589358608892558232457881464104718507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3758797728867444932557284604810000000000000)
      constant := (106472196787810292160298380097927294343965785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 223 interval.damping) (curvature.centralUpper 223 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree223.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 223 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel224
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51341347062530347921/12500000000000000000)
  centralHi := (410730776500242783369/100000000000000000000)
  directionLo := (205827403205823108117/50000000000000000000)
  directionHi := (82330961282329243247/20000000000000000000)

def endpointA : IntegerEndpointWitness 224 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree224.table
  base := (-148087482898001747250289831826694455241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-59914624027331734174017796520000000000000)
      constant := (1657430883997600253538328788512693222179036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 224 interval.damping) (curvature.centralUpper 224 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree224.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 224 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree224.table
  base := (-148087482901612152347046504414778928141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-77058070482635821867034575570000000000000)
      constant := (2193349685410422656565072659253926105359295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 224 interval.damping) (curvature.centralUpper 224 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree224.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 224 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel225
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205827403205823108117/50000000000000000000)
  centralHi := (82330961282329243247/20000000000000000000)
  directionLo := (6446511981552706427/1562500000000000000)
  directionHi := (412576766819373211329/100000000000000000000)

def endpointA : IntegerEndpointWitness 225 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree225.table
  base := (-5714895112117431451264491867986742967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-60185222833390628442706837760000000000000)
      constant := (1672989995625885616402810411190056106056264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 225 interval.damping) (curvature.centralUpper 225 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree225.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 225 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree225.table
  base := (-5714895113701282742715195236010378733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3792893178430865610412103801050000000000000)
      constant := (108480739258226179919570673137584354914420830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 225 interval.damping) (curvature.centralUpper 225 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree225.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 225 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel226
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6446511981552706427/1562500000000000000)
  centralHi := (412576766819373211329/100000000000000000000)
  directionLo := (103374167891586009283/25000000000000000000)
  directionHi := (413496671566344037133/100000000000000000000)

def endpointA : IntegerEndpointWitness 226 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree226.table
  base := (63191853727128631801522099974712523297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-60455821639449522711395879000000000000000)
      constant := (1688621380175704603803095543519797700186376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 226 interval.damping) (curvature.centralUpper 226 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree226.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 226 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree226.table
  base := (6319185372573901559637703158833559327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3809940903212575949339513399170000000000000)
      constant := (109492010804225948152010607683042284440702300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 226 interval.damping) (curvature.centralUpper 226 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree226.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 226 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel227
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103374167891586009283/25000000000000000000)
  centralHi := (413496671566344037133/100000000000000000000)
  directionLo := (207207267170919057631/50000000000000000000)
  directionHi := (414414534341838115263/100000000000000000000)

def endpointA : IntegerEndpointWitness 227 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree227.table
  base := (132676499152011532378737714170250526969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-60726420445508416980084920240000000000000)
      constant := (1704325037599723409469148368338362004215752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 227 interval.damping) (curvature.centralUpper 227 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree227.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 227 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree227.table
  base := (66338249575396176772241690528222991079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3826988627994286288266922997290000000000000)
      constant := (110507949220210820861011721616683658531257420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 227 interval.damping) (curvature.centralUpper 227 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree227.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 227 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel228
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207207267170919057631/50000000000000000000)
  centralHi := (414414534341838115263/100000000000000000000)
  directionLo := (83066073736774162253/20000000000000000000)
  directionHi := (207665184341935405633/50000000000000000000)

def endpointA : IntegerEndpointWitness 228 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree228.table
  base := (405478070618493840910196916329750322639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-60997019251567311248773961480000000000000)
      constant := (1720100967851115758602366614505319001290556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 228 interval.damping) (curvature.centralUpper 228 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree228.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 228 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree228.table
  base := (10136951765408864703084941338215374521/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3844036352775996627194332595410000000000000)
      constant := (111528554503312690142424461475570510670305800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 228 interval.damping) (curvature.centralUpper 228 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree228.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 228 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel229
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83066073736774162253/20000000000000000000)
  centralHi := (207665184341935405633/50000000000000000000)
  directionLo := (416244187981523159631/100000000000000000000)
  directionHi := (26015261748845197477/6250000000000000000)

def endpointA : IntegerEndpointWitness 229 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree229.table
  base := (27337945640804475002052163699579496569/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-61267618057626205517463002720000000000000)
      constant := (1735949170883555330834669620460966359725520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 229 interval.damping) (curvature.centralUpper 229 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree229.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 229 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree229.table
  base := (546758912814212695574906705169587640289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3861084077557706966121742193530000000000000)
      constant := (112553826650694070126462147951800548971870805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 229 interval.damping) (curvature.centralUpper 229 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree229.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 229 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel230
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416244187981523159631/100000000000000000000)
  centralHi := (26015261748845197477/6250000000000000000)
  directionLo := (417156005477225657133/100000000000000000000)
  directionHi := (208578002738612828567/50000000000000000000)

def endpointA : IntegerEndpointWitness 230 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree230.table
  base := (344597756719180234493305195344090448633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-61538216863685099786152043960000000000000)
      constant := (1751869646651208327873403769762752723589064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 230 interval.damping) (curvature.centralUpper 230 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree230.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 230 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree230.table
  base := (689195513436713944293899178024192594161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3878131802339417305049151791650000000000000)
      constant := (113583765659547641767263130334315927185569445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 230 interval.damping) (curvature.centralUpper 230 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree230.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 230 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel231
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417156005477225657133/100000000000000000000)
  centralHi := (208578002738612828567/50000000000000000000)
  directionLo := (104516458567249306621/25000000000000000000)
  directionHi := (83613166853799445297/20000000000000000000)

def endpointA : IntegerEndpointWitness 231 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree231.table
  base := (832787861148164934947925325232272510097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-61808815669743994054841085200000000000000)
      constant := (1767862395108726182467373170645929090040388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 231 interval.damping) (curvature.centralUpper 231 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree231.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 231 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree231.table
  base := (166557572229344092117288189654173936969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-79493459737165870285235946730000000000000)
      constant := (2339150439328485842566783566587354348424225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 231 interval.damping) (curvature.centralUpper 231 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree231.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 231 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel232
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104516458567249306621/25000000000000000000)
  centralHi := (83613166853799445297/20000000000000000000)
  directionLo := (104743421828160105293/25000000000000000000)
  directionHi := (418973687312640421173/100000000000000000000)

def endpointA : IntegerEndpointWitness 232 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree232.table
  base := (122191993090985074910006871418170044579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-62079414475802888323530126440000000000000)
      constant := (1783927416211238405421998090685381441426528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 232 interval.damping) (curvature.centralUpper 232 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree232.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 232 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree232.table
  base := (61095996545413337691415932041592951121/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3912227251902837982903970987890000000000000)
      constant := (115657644250590247065849421346899044368394320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 232 interval.damping) (curvature.centralUpper 232 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree232.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 232 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel233
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104743421828160105293/25000000000000000000)
  centralHi := (418973687312640421173/100000000000000000000)
  directionLo := (104969894355973478061/25000000000000000000)
  directionHi := (83975915484778782449/20000000000000000000)

def endpointA : IntegerEndpointWitness 233 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree233.table
  base := (1123439753077650148008260012807608289763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-62350013281861782592219167680000000000000)
      constant := (1800064709914345567481379572616230433159052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 233 interval.damping) (curvature.centralUpper 233 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree233.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 233 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree233.table
  base := (561719876538269246014609088165949749111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3929274976684548321831380586010000000000000)
      constant := (116701583827311499808969345977427315377064390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 233 interval.damping) (curvature.centralUpper 233 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree233.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 233 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel234
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104969894355973478061/25000000000000000000)
  centralHi := (83975915484778782449/20000000000000000000)
  directionLo := (52597939660067908583/12500000000000000000)
  directionHi := (84156703456108653733/20000000000000000000)

def endpointA : IntegerEndpointWitness 234 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree234.table
  base := (158812409401707458150806945787156921959/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-62620612087920676860908208920000000000000)
      constant := (1816274276174112412981813276905189021502688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 234 interval.damping) (curvature.centralUpper 234 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree234.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 234 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree234.table
  base := (317624818803171118639706261656038233247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3946322701466258660758790184130000000000000)
      constant := (117750190254568530758164978759666917468582060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 234 interval.damping) (curvature.centralUpper 234 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree234.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 234 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel235
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52597939660067908583/12500000000000000000)
  centralHi := (84156703456108653733/20000000000000000000)
  directionLo := (105421379856122753679/25000000000000000000)
  directionHi := (421685519424491014717/100000000000000000000)

def endpointA : IntegerEndpointWitness 235 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree235.table
  base := (283742900053289847283864159190767542107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-62891210893979571129597250160000000000000)
      constant := (1832556114947061102265477920208815350842140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 235 interval.damping) (curvature.centralUpper 235 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree235.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 235 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree235.table
  base := (1418714500265593773293728324408897469539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3963370426247968999686199782250000000000000)
      constant := (118803463529698322806983671629830179880037055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 235 interval.damping) (curvature.centralUpper 235 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree235.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 235 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel236
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105421379856122753679/25000000000000000000)
  centralHi := (421685519424491014717/100000000000000000000)
  directionLo := (211292798131893460289/50000000000000000000)
  directionHi := (422585596263786920579/100000000000000000000)

def endpointA : IntegerEndpointWitness 236 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree236.table
  base := (1568085417479255009596687374310631970437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-63161809700038465398286291400000000000000)
      constant := (1848910226190164579924172829217242527881748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 236 interval.damping) (curvature.centralUpper 236 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree236.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 236 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree236.table
  base := (784042708739252293610583682449479545337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3980418151029679338613609380370000000000000)
      constant := (119861403650065469314177298229944244977215130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 236 interval.damping) (curvature.centralUpper 236 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree236.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 236 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel237
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211292798131893460289/50000000000000000000)
  centralHi := (422585596263786920579/100000000000000000000)
  directionLo := (423483760074619455831/100000000000000000000)
  directionHi := (52935470009327431979/12500000000000000000)

def endpointA : IntegerEndpointWitness 237 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree237.table
  base := (1718612016206382000757904557085043028249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-63432408506097359666975332640000000000000)
      constant := (1865336609860840066021975400953340172112996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 237 interval.damping) (curvature.centralUpper 237 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree237.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 237 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree237.table
  base := (1718612016205723732313921371629816968421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-3997465875811389677541018978490000000000000)
      constant := (120924010613061775449659189464875305157263145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 237 interval.damping) (curvature.centralUpper 237 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree237.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 237 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel238
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423483760074619455831/100000000000000000000)
  centralHi := (52935470009327431979/12500000000000000000)
  directionLo := (10609500575081732751/2500000000000000000)
  directionHi := (424380023003269310041/100000000000000000000)

def endpointA : IntegerEndpointWitness 238 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree238.table
  base := (467573571477901737658919833925791925863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-63703007312156253935664373880000000000000)
      constant := (1881835265916942667521816463382812670813808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 238 interval.damping) (curvature.centralUpper 238 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree238.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 238 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree238.table
  base := (1870294285911029528878771279709548476929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-81928848991695918703437317890000000000000)
      constant := (2489618049308282997998051156402547742384645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 238 interval.damping) (curvature.centralUpper 238 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree238.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 238 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel239
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10609500575081732751/2500000000000000000)
  centralHi := (424380023003269310041/100000000000000000000)
  directionLo := (425274397068025859809/100000000000000000000)
  directionHi := (42527439706802585981/10000000000000000000)

def endpointA : IntegerEndpointWitness 239 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree239.table
  base := (2023132216166610557062570811821615742677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-63973606118215148204353415120000000000000)
      constant := (1898406194316759107215026252912286462970708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 239 interval.damping) (curvature.centralUpper 239 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree239.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 239 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree239.table
  base := (202313221616610406089707927865665489269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4031561325374810355395838174730000000000000)
      constant := (123063225056642805781488683562924880448709050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 239 interval.damping) (curvature.centralUpper 239 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree239.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 239 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel240
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425274397068025859809/100000000000000000000)
  centralHi := (42527439706802585981/10000000000000000000)
  directionLo := (85233378832213487537/20000000000000000000)
  directionHi := (213083447080533718843/50000000000000000000)

def endpointA : IntegerEndpointWitness 240 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree240.table
  base := (1088562898324719212867666196987820569517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-64244204924274042473042456360000000000000)
      constant := (1915049395019001567524391783175902564556136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 240 interval.damping) (curvature.centralUpper 240 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree240.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 240 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree240.table
  base := (2177125796648994150450241359107683457673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4048609050156520694323247772850000000000000)
      constant := (124139832532143713559821662180181382447129885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 240 interval.damping) (curvature.centralUpper 240 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree240.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 240 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel241
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85233378832213487537/20000000000000000000)
  centralHi := (213083447080533718843/50000000000000000000)
  directionLo := (85411505210061247017/20000000000000000000)
  directionHi := (213528763025153117543/50000000000000000000)

def endpointA : IntegerEndpointWitness 241 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree241.table
  base := (233227501714299009938072726125944257827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-64514803730332936741731497600000000000000)
      constant := (1931764867982801646620820106890037770313080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 241 interval.damping) (curvature.centralUpper 241 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree241.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 241 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree241.table
  base := (583068754285650101913862999493689068931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4065656774938231033250657370970000000000000)
      constant := (125221106840105400886382155162337815287552380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 241 interval.damping) (curvature.centralUpper 241 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree241.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 241 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel242
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85411505210061247017/20000000000000000000)
  centralHi := (213528763025153117543/50000000000000000000)
  directionLo := (427946304381198648859/100000000000000000000)
  directionHi := (21397315219059932443/5000000000000000000)

def endpointA : IntegerEndpointWitness 242 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree242.table
  base := (2488579867533535542121735590733928982487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-64785402536391831010420538840000000000000)
      constant := (1948552613167704424360803144762935715929948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 242 interval.damping) (curvature.centralUpper 242 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree242.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 242 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree242.table
  base := (2488579867533193733263547491441419564719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4082704499719941372178066969090000000000000)
      constant := (126307047978050004131854117401959147793356155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 242 interval.damping) (curvature.centralUpper 242 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree242.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 242 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel243
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427946304381198648859/100000000000000000000)
  centralHi := (21397315219059932443/5000000000000000000)
  directionLo := (428833240678521859347/100000000000000000000)
  directionHi := (107208310169630464837/25000000000000000000)

def endpointA : IntegerEndpointWitness 243 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree243.table
  base := (2646040337809258472204458004122435430339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-65056001342450725279109580080000000000000)
      constant := (1965412630533662635617325299281489741721356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 243 interval.damping) (curvature.centralUpper 243 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree243.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 243 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree243.table
  base := (2646040337808958667389073318969733360001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4099752224501651711105476567210000000000000)
      constant := (127397655943524628508565612541513584673200245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 243 interval.damping) (curvature.centralUpper 243 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree243.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 243 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel244
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428833240678521859347/100000000000000000000)
  centralHi := (107208310169630464837/25000000000000000000)
  directionLo := (214859173174058703287/50000000000000000000)
  directionHi := (17188733853924696263/4000000000000000000)

def endpointA : IntegerEndpointWitness 244 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree244.table
  base := (2804656418058825951986027978359566519719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-65326600148509619547798621320000000000000)
      constant := (1982344920041030948639815104353438266078876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 244 interval.damping) (curvature.centralUpper 244 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree244.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 244 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree244.table
  base := (701164104514640748386239180446391137339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4116799949283362050032886165330000000000000)
      constant := (128492930734100997623477307755101463314592220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 244 interval.damping) (curvature.centralUpper 244 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree244.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 244 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel245
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214859173174058703287/50000000000000000000)
  centralHi := (17188733853924696263/4000000000000000000)
  directionLo := (53825204084825313853/12500000000000000000)
  directionHi := (17224065307144100433/4000000000000000000)

def endpointA : IntegerEndpointWitness 245 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree245.table
  base := (2964428098469983659495859067047643068719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-65597198954568513816487662560000000000000)
      constant := (1999349481650560346140390214193190572274876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 245 interval.damping) (curvature.centralUpper 245 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree245.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 245 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree245.table
  base := (741107024617438255633251182668531239063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-84364238246225967121638689050000000000000)
      constant := (2644752496885206312708890729903370624781260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 245 interval.damping) (curvature.centralUpper 245 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree245.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 245 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel246
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53825204084825313853/12500000000000000000)
  centralHi := (17224065307144100433/4000000000000000000)
  directionLo := (215741555421524931947/50000000000000000000)
  directionHi := (86296622168609972779/20000000000000000000)

def endpointA : IntegerEndpointWitness 246 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree246.table
  base := (3125355369328176280677809255082309194599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-65867797760627408085176703800000000000000)
      constant := (2016426315323392606862826060740329236778396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 246 interval.damping) (curvature.centralUpper 246 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree246.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 246 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree246.table
  base := (1562677684663986997753784882526688639579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4150895398846782727887705361570000000000000)
      constant := (130697480780966897690423442914762077433393710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 246 interval.damping) (curvature.centralUpper 246 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree246.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 246 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel247
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215741555421524931947/50000000000000000000)
  centralHi := (86296622168609972779/20000000000000000000)
  directionLo := (86472558380127319629/20000000000000000000)
  directionHi := (216181395950318299073/50000000000000000000)

def endpointA : IntegerEndpointWitness 247 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree247.table
  base := (328743822101519247591113666446474064553/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-66138396566686302353865745040000000000000)
      constant := (2033575421021054885448639676482858962582120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 247 interval.damping) (curvature.centralUpper 247 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree247.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 247 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree247.table
  base := (821859555253753764998607639501540884919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4167943123628493066815114959690000000000000)
      constant := (131806756032519901067684514993197510067220620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 247 interval.damping) (curvature.centralUpper 247 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree247.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 247 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel248
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86472558380127319629/20000000000000000000)
  centralHi := (216181395950318299073/50000000000000000000)
  directionLo := (216620343399131560881/50000000000000000000)
  directionHi := (433240686798263121763/100000000000000000000)

def endpointA : IntegerEndpointWitness 248 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree248.table
  base := (3450676644007833888368374293023056958113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-66408995372745196622554786280000000000000)
      constant := (2050796798705454388470521193412092227832452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 248 interval.damping) (curvature.centralUpper 248 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree248.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 248 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree248.table
  base := (3450676644007678286584720168247816812341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4184990848410203405742524557810000000000000)
      constant := (132920698099700935961813689599956715119023545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 248 interval.damping) (curvature.centralUpper 248 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree248.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 248 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel249
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216620343399131560881/50000000000000000000)
  centralHi := (433240686798263121763/100000000000000000000)
  directionLo := (217058403186071245273/50000000000000000000)
  directionHi := (434116806372142490547/100000000000000000000)

def endpointA : IntegerEndpointWitness 249 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree249.table
  base := (56485478576196994927513336897929656401/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-66679594178804090891243827520000000000000)
      constant := (2068090448338873144557715937210869992038656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 249 interval.damping) (curvature.centralUpper 249 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree249.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 249 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree249.table
  base := (1807535314438235603798301578436987899149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4202038573191913744669934155930000000000000)
      constant := (134039306980199776718228917052508124070583010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 249 interval.damping) (curvature.centralUpper 249 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree249.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 249 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel249
