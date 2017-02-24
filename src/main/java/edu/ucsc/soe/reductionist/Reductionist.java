package edu.ucsc.soe.reductionist;

import automata.svpa.SVPA;
import automata.svpa.SVPAMove;
//import sometheory 
import org.roaringbitmap.RoaringBitmap;

import java.io.FileReader;
import javax.json.*;

public class Reductionist {
    public static void main(String[] args) {
    }

    public static Reductionist fromJSONFile(String path)
        throws java.io.FileNotFoundException, java.io.IOException {
        FileReader fread = new FileReader(path);
        JsonReader jread = Json.createReader(fread);
        JsonObject jobj = jread.readObject();
        Reductionist r = new Reductionist();
        System.out.println(jobj.getJsonObject("markups").toString());
        jread.close();
        fread.close();
        return r;
    }

    protected Reductionist() {

    }
}
