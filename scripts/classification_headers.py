"""One checked header table for all 342 empty classification roots."""
from generate_five_colour_projection import encoded_header
from classification_projection import projected_row


def generate_headers(info, rows, projections, dest):
    empty=[i for i,entry in enumerate(info['roots']) if not entry['terminals']]
    if len(empty)!=342:raise ValueError('unexpected empty-root count')
    chosen=[]
    for i in empty:
        original=info['roots'][i]['original_root']
        if original in projections:
            row=projections[original][1]
        else:
            row=projected_row(rows[i],rows[i][5])
            if row!=rows[i]:raise ValueError('identity projection changes the stored header')
        chosen.append(row)
    vector=lambda values:'!['+','.join(map(str,values))+']'
    text='''module
public import FiveColour.ProjectionBridge
@[expose] public section
namespace FiveColour.Packed.ClassificationProjected
set_option maxHeartbeats 0
set_option maxRecDepth 100000
'''
    text+='def caseNumbers : Fin 342 → Fin 357 := '+vector(info['roots'][i]['original_root'] for i in empty)+'\n'
    text+='def goals : Fin 342 → Nat := '+vector(row[3] for row in chosen)+'\n'
    text+='def budgets : Fin 342 → Nat := '+vector(row[5] for row in chosen)+'\n'
    text+='def headers : Array Archive.Header := #[\n  '+',\n  '.join('⟨'+','.join(map(str,encoded_header(row)))+'⟩' for row in chosen)+']\n'
    text+='''
abbrev root (i : Fin 342) : Box := Projection.root headers[i.val]!
abbrev families (i : Fin 342) : Fin 78 → List Cut := Projection.families (goals i) headers[i.val]!
abbrev HeaderValid (i : Fin 342) : Prop :=
  Projection.HeaderValid 14 (caseNumbers i) (budgets i) (goals i) headers[i.val]!
end FiveColour.Packed.ClassificationProjected
'''
    (dest/'Headers.lean').write_text(text)
    groups=(len(empty)+49)//50
    for g in range(groups):
        text='''module
public import FiveColour.EnumerationChunks.Headers
@[expose] public section
namespace FiveColour.Packed.ClassificationProjected
set_option maxHeartbeats 0
set_option maxRecDepth 100000
'''
        text+=''.join(f'lemma header_valid_{j} : HeaderValid {j} := by decide +kernel\n' for j in range(g*50,min(g*50+50,len(empty))))
        text+='end FiveColour.Packed.ClassificationProjected\n'
        (dest/f'HeaderChecks{g}.lean').write_text(text)
    text='module\n'+''.join(f'public import FiveColour.EnumerationChunks.HeaderChecks{g}\n' for g in range(groups))
    text+='''@[expose] public section
namespace FiveColour.Packed.ClassificationProjected
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem header_valid (i : Fin 342) : HeaderValid i := by
  fin_cases i
'''+''.join(f'  · exact header_valid_{j}\n' for j in range(len(empty)))+'end FiveColour.Packed.ClassificationProjected\n'
    (dest/'HeaderChecks.lean').write_text(text)
    return {case:j for j,case in enumerate(empty)}
