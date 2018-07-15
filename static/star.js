
function allOf(l,f){
    for (c of l) if (!f(c)) return false;
    return true;
}

function joincards(cs){//TODO: debug
    if(cs.length==0)return "0"
    topc = cs[0];
    rest=cs.slice(1);
    if (rest.length==0) return showCard(topc)
    if (! allOf(cs,c=>c.tag=="CardBack")) return showCard(topc)+" "+joincards(rest)
    return (showCard(topc)+cs.length)
}

function displayHand(h){
    s = "<div class=hand>"
    s+=h[0]
    s+="<p>"+joincards(h[1])+"</p>"
    s+="</div>"
    return s
}
function displayOwnHand(h){
    s = "<div class=hand>"
    s+=h[0]+"<br />"
    s+=h[1].map(tagCard).join(" ")
    s+="</div>"
    return s
}

function tagCard(c,i){
    //let x = showCard(c)
    //console.log(c)
    sh = showCard(c)
    c = c.contents
    return "<a onclick=sendC("+i+")>"+sh+"</a>"
}

function sendC(card){
    sendMove("ReqPlay",card)
}

function draw(){
    n=$("#drawN").val() - 0
    sendMove("ReqDraw",n)
    $("#drawN").val(1)
}

function sendMove(type,dat){
    $.post("",JSON.stringify({
        tag:type,
        contents:[name,tok,dat,$("#mmsg").val()]
    }),display,"json")
    $("#mmsg").val("")
}

function showCard(c){
    if (c.tag=="CardBack") return String.fromCodePoint(0x1f0a0)
    else if (c.tag=="CardFace") return "<span class="+c.contents[1]+">"+String.fromCodePoint(
        0x1f0a0 + suitNums[c.contents[1]]*16 + rankNums[c.contents[0]])+"</span>"
    else console.log("unrecognised card")
}

rankNums = {"Ace": 1,
"Two": 2,
"Three": 3,
"Four": 4,
"Five": 5,
"Six": 6,
"Seven": 7,
"Eight": 8,
"Nine": 9,
"Ten": 10,
"Jack": 11,
"Knight": 12,
"Queen": 13,
"King":14}

suitNums = {
    "Spades" : 0,
    "Hearts" : 1,
    "Diamonds" : 2,
    "Clubs" : 3}

//https://stackoverflow.com/a/901144/1779797
function getParameterByName(name, url) {
    if (!url) url = window.location.href;
    var name = name.replace(/[\[\]]/g, "\\$&");
    var regex = new RegExp("[?&]" + name + "(=([^&#]*)|&|#|$)"),
        results = regex.exec(url);
    if (!results) return null;
    if (!results[2]) return '';
    return decodeURIComponent(results[2].replace(/\+/g, " "));
}


function randstr(n) {
  var text = "";
  for (var i = 0; i < n; i++)
    text += String.fromCharCode(Math.floor(Math.random()*(127-32)+32));
  return text;
}