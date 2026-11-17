package petri

import (
	"fmt"
	"html"
	"strings"
)

// ExportPNML serializes a compiled PetriNet (and optional all workflow nets) to ISO PNML XML.
func ExportPNML(nets []*PetriNet) string {
	var sb strings.Builder
	sb.WriteString(`<?xml version="1.0" encoding="UTF-8"?>` + "\n")
	sb.WriteString(`<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">` + "\n")
	for _, net := range nets {
		sb.WriteString(fmt.Sprintf(`  <net id="%s" type="http://www.pnml.org/version-2009/grammar/ptnet">`+"\n", html.EscapeString(net.Name)))
		sb.WriteString("    <page id=\"page0\">\n")
		for _, pl := range net.Places {
			pid := fmt.Sprintf("p%d", pl.ID)
			sb.WriteString(fmt.Sprintf(`      <place id="%s"><name><text>%s</text></name>`, pid, html.EscapeString(pl.Name)))
			if pl.InitTokens > 0 {
				sb.WriteString(fmt.Sprintf(`<initialMarking><text>%d</text></initialMarking>`, pl.InitTokens))
			}
			sb.WriteString("</place>\n")
		}
		for _, tr := range net.Transitions {
			tid := fmt.Sprintf("t%d", tr.ID)
			sb.WriteString(fmt.Sprintf(`      <transition id="%s"><name><text>%s</text></name></transition>`+"\n", tid, html.EscapeString(tr.Name)))
		}
		arcIdx := 0
		for _, tr := range net.Transitions {
			tid := fmt.Sprintf("t%d", tr.ID)
			for p, w := range tr.Pre {
				arcIdx++
				sb.WriteString(fmt.Sprintf(`      <arc id="a%d" source="p%d" target="%s"><inscription><text>%d</text></inscription></arc>`+"\n", arcIdx, p, tid, w))
			}
			for p, w := range tr.Post {
				arcIdx++
				sb.WriteString(fmt.Sprintf(`      <arc id="a%d" source="%s" target="p%d"><inscription><text>%d</text></inscription></arc>`+"\n", arcIdx, tid, p, w))
			}
		}
		sb.WriteString("    </page>\n  </net>\n")
	}
	sb.WriteString("</pnml>\n")
	return sb.String()
}
