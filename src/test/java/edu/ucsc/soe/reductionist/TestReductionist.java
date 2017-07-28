package edu.ucsc.soe.reductionist;

import automata.AutomataException;
import automata.svpa.SVPA;
import automata.svpa.TaggedSymbol;
import org.junit.Test;
import org.roaringbitmap.RoaringBitmap;
import org.sat4j.specs.TimeoutException;
import theory.svpa.equalityalgebra.EqualityPredicate;

import javax.json.Json;
import javax.json.JsonArrayBuilder;
import javax.json.JsonObjectBuilder;
import javax.json.JsonWriter;
import java.io.FileWriter;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

public class TestReductionist {

    public void outputResults(JsonObjectBuilder outp, Reductionist.Cardinalities cards, String netCardKey, String cardKey) {
        outp.add(netCardKey, cards.total);
        JsonArrayBuilder cs = Json.createArrayBuilder();
        for(int i = 0; i < cards.cards.length; i++) {
            cs.add(cards.cards[i]);
        }
        outp.add(cardKey, cs);
    }

    void doCheck(Reductionist r, Collection<String> tagsIn, Collection<String> tagsOut, JsonObjectBuilder outs, String key) throws TimeoutException, AutomataException {
        long startTime = System.nanoTime();
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> prop =
                r.tagSetProperty(tagsIn).
                        intersectionWith(
                                r.tagSetAbsentProperty(tagsOut), r.theory);
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> svpa = r.svpa.intersectionWith(prop, r.theory);
        long midTime = System.nanoTime();
        List<TaggedSymbol<RoaringBitmap>> witness = r.witnessForProperty(prop);
        long endTime = System.nanoTime();
        long propT = midTime - startTime;
        long checkT = endTime - startTime;
        JsonObjectBuilder results = Json.createObjectBuilder();
        outs.add(key+"Build", propT/1000000.0);
        outs.add(key+"Check", checkT/1000000.0);

        Reductionist.Cardinalities cards = r.getCardinalities(svpa, 6000);
        outputResults(outs, cards, key+"NetCards", key+"Cards");
    }

    @Test
    public void CreateSVPA () throws Exception {
        JsonObjectBuilder results = Json.createObjectBuilder();
        int lim = 6000;

        JsonObjectBuilder ttSmallResults = Json.createObjectBuilder();

        long a,b;
        a = System.nanoTime();
        Reductionist talktownSmall = Reductionist.fromJSONFile("int10_experiment_benchmarks/talktown.json", false);
        b = System.nanoTime();
        ttSmallResults.add("constructionTime", (b-a)/1000000.0);
        a = System.nanoTime();
        Reductionist.Cardinalities pCards = talktownSmall.getCardinalities(talktownSmall.svpa, lim);
        b = System.nanoTime();
        ttSmallResults.add("cardsTime", (b-a)/1000000.0);
        outputResults(ttSmallResults, pCards, "netCards", "cards");

        a = System.nanoTime();
        talktownSmall = Reductionist.fromJSONFile("int10_experiment_benchmarks/talktown.json", true);
        b = System.nanoTime();
        ttSmallResults.add("constructionTimeEMs", (b-a)/1000000.0);

        Collection<String> tags, tagsIn, tagsOut;
        SVPA<EqualityPredicate<FiniteSetPred, RoaringBitmap>, RoaringBitmap> prop;
        List<TaggedSymbol<RoaringBitmap>> witness;

        System.out.println("E1");
        tagsIn = Arrays.asList("Moves:request name", "PushObligation:introduce self");
        tagsOut = Arrays.asList("Moves:say nice to meet you", "Moves:say rude remark");
        doCheck(talktownSmall, tagsIn, tagsOut, ttSmallResults, "easy");

        //hard
        boolean hard = false;
        if(hard) {
            System.out.println("H1");
            tagsIn = Arrays.asList(
                    "Moves:introduce self",
                    "PushObligation:repair incorrect first name usage",
                    "Propositions:subject=interlocutor;feature_type=first name;feature_value=speaker.belief(interlocutor, 'first name');feature_object_itself=None",
                    "Propositions:subject=speaker;feature_type=first name;feature_value=speaker.first_name;feature_object_itself=None",
                    "ViolationConditions:awkward rehash<--lambda conversation: conversation.earlier_move(conversation.speaker, 'introduce self')",
                    "Moves:say nice to meet you",
                    "Moves:say first name",
                "Preconditions:lambda speaker, interlocutor: speaker.belief(interlocutor, 'first name')",
                "PushObligation:say nice to meet you",
                "Preconditions:lambda conversation: conversation.earlier_move(conversation.interlocutor, 'introduce self')",
                "Moves:introduce self back",
                "Preconditions:lambda conversation: conversation.last_interlocutor_turn.performed_move('say nice to meet you')",
                "Preconditions:lambda speaker, interlocutor: speaker.inaccurate_belief(interlocutor, 'first name')",
                //"Context:NULL",
                "Preconditions:lambda speaker: speaker.personality.high_e",
                "Preconditions:lambda speaker, interlocutor: interlocutor in speaker.relationships",
                "Preconditions:lambda conversation: conversation.has_obligation(conversation.speaker, 'say nice to meet you')",
                    "Preconditions:lambda conversation: conversation.earlier_move(conversation.interlocutor, 'say first name')"
            );

//        System.out.println("H2");
            tagsOut = Arrays.asList(
                    "Preconditions:lambda speaker: speaker.moves",
                    "Preconditions:lambda conversation: len(conversation.turns) >= 6",
                    "Preconditions:lambda speaker: speaker.mind.preoccupation and speaker.belief(speaker.mind.preoccupation, 'first name')",
                    "Preconditions:lambda conversation: not conversation.speaker.belief(conversation.speaker_subject_match, 'first name')",
                    "Moves:ask do you know someone",
                    "Preconditions:lambda conversation: conversation.last_turn and conversation.last_turn.speaker is conversation.speaker",
                    "Context:subject:first_name=speaker.belief(speaker.mind.preoccupation, 'first name')",
                "Preconditions:lambda speaker, interlocutor: interlocutor not in speaker.mind.mental_models",
                "Moves:respond about the weather",
                "ViolationConditions:awkward rehash<--lambda conversation: conversation.earlier_move('either', 'reask about the weather')",
                "Preconditions:lambda conversation: conversation.earlier_move(conversation.speaker, 'assert about the weather')",
                "Preconditions:lambda conversation: conversation.earlier_move(conversation.interlocutor, 'ask how are you')",
                "Preconditions:lambda speaker: speaker.male and speaker.occupation and speaker.occupation.level < 2",
                "Preconditions:lambda speaker: speaker.personality.cold",
                "Moves:ask how are you",
                "PushObligation:redress incorrect first name usage",
                "Context:subject:last_name=speaker.belief(speaker.mind.preoccupation, 'last name')",
                    "Preconditions:lambda conversation: not conversation.earlier_move(conversation.interlocutor, 'say first name')"
            );
            doCheck(talktownSmall, tagsIn, tagsOut, ttSmallResults, "hard");
        }
        results.add("talktown-small", ttSmallResults);

        JsonObjectBuilder hackResults = Json.createObjectBuilder();
        a = System.nanoTime();
        Reductionist hackers = Reductionist.fromJSONFile("int10_experiment_benchmarks/HackerTexts.json", false);
        b = System.nanoTime();
        hackResults.add("constructionTime", (b-a)/1000000.0);
        a = System.nanoTime();
        pCards = hackers.getCardinalities(hackers.svpa, lim);
        b = System.nanoTime();
        hackResults.add("cardsTime", (b-a)/1000000.0);
        outputResults(hackResults, pCards, "netCards", "cards");

        a = System.nanoTime();
        hackers = Reductionist.fromJSONFile("int10_experiment_benchmarks/HackerTexts.json", true);
        b = System.nanoTime();
        hackResults.add("constructionTimeEMs", (b-a)/1000000.0);

        System.out.println("E1");
        tagsIn = Arrays.asList("relationship:== Work", "linkSuspicion:ClearlySuspicious");
        tagsOut = Arrays.asList("jerk:> 2", "directness:>= 2");
        doCheck(hackers, tagsIn, tagsOut, hackResults, "easy");
        //hard
        boolean hard2 = false;
        if(hard2) {
            System.out.println("H1");
            tagsIn = Arrays.asList(
                    "jerk:> 2",
                    "jerk:>= 1",
                    "directness:> 2",
                    "relationship:== Work",
                    "directness:>= 2",
                    "jerk:<= 3",
                    "assertiveness:>= 2",
                    "linkSuspicion:Suggestive"
            );

//        System.out.println("H2");
            tagsOut = Arrays.asList(
                    "linkSuspicion:Amiguous",
                    "directness:<= 3",
                    "relationship:== Communities",
                    "relationship:== Family",
                    "jerk:< 2",
                    "jerk:>= 2",
                    "directness:>= 1",
                    "assertiveness:<= 3"
            );
            doCheck(hackers, tagsIn, tagsOut, hackResults, "hard");
//            prop = hackers.
//                    tagSetProperty(tagsIn).
//                    intersectionWith(
//                            hackers.tagSetAbsentProperty(tagsOut),
//                            hackers.theory);
//            witness = hackers.witnessForProperty(prop);
//        pCards = talktownSmall.getCardinalities(prop, lim);
//        outputResults(ttSmallResults, pCards, "netCardsHard2", "cardsHard2");
        }
        results.add("hackers", hackResults);



        JsonObjectBuilder jukeResults = Json.createObjectBuilder();
        a = System.nanoTime();
        Reductionist juke = Reductionist.fromJSONFile("int10_experiment_benchmarks/jukejoint.json", false);
        b = System.nanoTime();
        jukeResults.add("constructionTime", (b-a)/1000000.0);
        a = System.nanoTime();
        pCards = juke.getCardinalities(juke.svpa, lim);
        b = System.nanoTime();
        jukeResults.add("cardsTime", (b-a)/1000000.0);
        outputResults(jukeResults, pCards, "netCards", "cards");

        a = System.nanoTime();
        juke = Reductionist.fromJSONFile("int10_experiment_benchmarks/jukejoint.json", true);
        b = System.nanoTime();
        jukeResults.add("constructionTimeEMs", (b-a)/1000000.0);

        System.out.println("E1");
        tagsIn = Arrays.asList(
                "Signals:disappointment 1",
//                "Signals:do depart 1",
//                "Preconditions:lambda thinker: not ('do depart' in thinker.mind.receptors and thinker.mind.receptors['do depart'].voltage >= thinker.game.config.summative_thought_receptor_voltage_threshold)",
                "Preconditions:lambda thinker: not thinker.mind.thoughts",
                "Signals:this town 1"
        );
        tagsOut = Arrays.asList(
//                "Preconditions:lambda thinker: 'don\\'t depart' in thinker.mind.receptors and thinker.mind.receptors[\"don\\'t depart\"].most_associated_signals(n=3, excluding=[\"do depart\", \"no romance here\", \"disappointment\", \"commitment\", \"love\", \"deception\"])[0] == \\'this town\\'",
//                "Effects:lambda thinker: thinker.make_decision",
                "Preconditions:lambda thinker: thinker.love_interest",
                "Signals:no romance here 1",
                "Preconditions:lambda thinker: not thinker.spouse"
        );
        doCheck(juke, tagsIn, tagsOut, jukeResults, "easy");

        //hard
        boolean hard3 = false;
        if(hard3) {
            System.out.println("H1");
            tagsIn = Arrays.asList(
                    "Preconditions:lambda thinker: thinker.personality.gregarious",
                    "Signals:love 1",
                    "Signals:disappointment 1",
                    "Preconditions:lambda thinker: thinker.spouse",
                    "Signals:don't depart 1",
                    "Preconditions:lambda thinker: thinker.love_interest and thinker.love_interest is not thinker.spouse",
                    "Preconditions:lambda thinker: thinker.love_interest and thinker.love_interest.female",
                    "Preconditions:lambda thinker: len(thinker.friends) < 5",
                    "Signals:do depart 1",
                    "Preconditions:lambda thinker: not ('do depart' in thinker.mind.receptors and thinker.mind.receptors['do depart'].voltage >= thinker.game.config.summative_thought_receptor_voltage_threshold)",
                    "Preconditions:lambda thinker: not (\"don't depart\" in thinker.mind.receptors and thinker.mind.receptors[\"don't depart\"].voltage >= thinker.game.config.summative_thought_receptor_voltage_threshold)",
                    "Preconditions:lambda thinker: thinker.spouse and thinker.marriage.duration > 2",
                    "Preconditions:lambda thinker: len(thinker.friends) is 0",
                    "Signals:my partner 1",
                    "Preconditions:lambda thinker: thinker.requited_love_interest",
                    "Signals:commitment 1"
            );

//        System.out.println("H2");
            tagsOut = Arrays.asList(
                    "Preconditions:lambda thinker: \"don\\'t depart\" in thinker.mind.receptors and thinker.mind.receptors[\"don\\'t depart\"].most_associated_signals(n=3, excluding=[\"do depart\", \"no romance here\", \"disappointment\", \"commitment\", \"love\", \"deception\"])[0] == \\'my job\\'",
                    "Preconditions:lambda thinker: \\'do depart\\' in thinker.mind.receptors and thinker.mind.receptors[\\'do depart\\'].most_associated_signals(n=3, excluding=[\"don\\'t depart\", \\'disappointment\\', \\'commitment\\', \\'love\\', \\'deception\\'])[1] == \\'my partner\\'",
                    "Preconditions:lambda thinker: thinker.kids",
                    "Preconditions:lambda thinker: thinker.boss and thinker is not thinker.boss and thinker.dislikes(thinker.boss) and not thinker.hates(thinker.boss)",
                    "Signals:new job elsewhere 1",
                    "Preconditions:lambda thinker: not thinker.mind.last_thought_had_signal(\"don\\'t depart\")",
                    "Preconditions:lambda thinker: not thinker.personality.gregarious and not thinker.personality.cold",
                    "Preconditions:lambda thinker: thinker.occupation and thinker.occupation.years_experience > 2",
                    "Preconditions:lambda thinker: \"don\\'t depart\" in thinker.mind.receptors and thinker.mind.receptors[\"don\\'t depart\"].most_associated_signals(n=3, excluding=[\"do depart\", \"no romance here\", \"disappointment\", \"commitment\", \"love\", \"deception\"])[1] == \\'this town\\'",
                    "Preconditions:lambda thinker: thinker.age < 30 and thinker.boss and thinker.boss.age > 50",
                    "Preconditions:lambda thinker: thinker.mind.last_thought_had_signal(\\'dodepart\\')",
                    "Preconditions:lambda thinker: \\'do depart\\' in thinker.mind.receptors and thinker.mind.receptors[\\'do depart\\'].most_associated_signals(n=3, excluding=[\"don\\'t depart\", \\'disappointment\\', \\'commitment\\', \\'love\\', \\'deception\\'])[1] == \\'no romance here\\'",
                    "Preconditions:lambda thinker: \"don\\'t depart\" in thinker.mind.receptors and thinker.mind.receptors[\"don\\'t depart\"].most_associated_signals(n=3, excluding=[\"do depart\", \"no romance here\", \"disappointment\", \"commitment\", \"love\", \"deception\"])[0] == \\'my love interest\\'",
                    "Preconditions:lambda thinker: \"don\\'t depart\" in thinker.mind.receptors and thinker.mind.receptors[\"don\\'t depart\"].most_associated_signals(n=3, excluding=[\"do depart\", \"no romance here\", \"disappointment\", \"commitment\", \"love\", \"deception\"])[1] == \\'new job elsewhere\\'",
                    "Effects:lambda thinker: thinker.make_decision",
                    "Preconditions:lambda thinker: thinker.boss and thinker is not thinker.boss"
            );
            doCheck(juke, tagsIn, tagsOut, jukeResults, "hard");
        }
        results.add("juke", jukeResults);

        JsonObjectBuilder ttLargeResults = Json.createObjectBuilder();
        Reductionist talktownLarge = Reductionist.fromJSONFile("int10_experiment_benchmarks/talktown-aiide-study-2016.json", false);
        b = System.nanoTime();
        ttLargeResults.add("constructionTime", (b-a)/1000000.0);
        a = System.nanoTime();
        pCards = talktownLarge.getCardinalities(talktownLarge.svpa, lim);
        b = System.nanoTime();
        ttLargeResults.add("cardsTime", (b-a)/1000000.0);
        outputResults(ttLargeResults, pCards, "netCards", "cards");

        a = System.nanoTime();
        talktownLarge = Reductionist.fromJSONFile("int10_experiment_benchmarks/talktown-aiide-study-2016.json", true);
        b = System.nanoTime();
        ttLargeResults.add("constructionTimeEMs", (b-a)/1000000.0);

        results.add("talktown_large", ttLargeResults);

        //System.out.println(results.build().toString());
        FileWriter fw = new FileWriter("results.json");
        JsonWriter jw = Json.createWriter(fw);
        jw.write(results.build());
        jw.close();
        fw.close();
    }
}
