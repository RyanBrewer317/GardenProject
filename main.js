const firebaseConfig = {
    apiKey: "AIzaSyA_S5yn1yyl7ay8S_ZS8sO6RUpTamhaOUo",
    authDomain: "garden-project-1.firebaseapp.com",
    projectId: "garden-project-1",
    storageBucket: "garden-project-1.appspot.com",
    messagingSenderId: "747632810774",
    appId: "1:747632810774:web:8d6411f2c8cf3ee2714e37",
    measurementId: "G-ZL76K7TZBL"
};

const firebaseApp = firebase.initializeApp(firebaseConfig);
const db = firebase.firestore();

var app = Elm.Main.init({
    node: document.getElementById("myapp")
});

app.ports.requestPage.subscribe(pageName => {
    const query = db.collection("apps").where("name", "==", pageName);
    query.get().then(querySnapshot => querySnapshot.forEach(doc => {
        if (!doc.exists) {
            app.ports.pageReceiver.send("error 404");
            return;
        }
        app.ports.pageReceiver.send(doc.data().code);
    }));
});