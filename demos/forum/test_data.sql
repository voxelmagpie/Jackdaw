-- Database must be blank before running this
USE forum;

INSERT INTO Threads (title) VALUES ("Test thread...");
INSERT INTO Threads (title) VALUES ("Hello, people");

INSERT INTO Posts (thread_id, content) VALUES (1, "Maecenas ornare, tellus nec elementum ullamcorper, odio arcu consectetur mi, quis convallis ante metus id lectus.");
INSERT INTO Posts (thread_id, content) VALUES (1, "Proin nec aliquam massa. Suspendisse et ante vitae ante rutrum varius quis vitae massa.");
INSERT INTO Posts (thread_id, content) VALUES (1, "Etiam dictum dui ac mi fermentum elementum.");

INSERT INTO Posts (thread_id, content) VALUES (2, "Hello");
INSERT INTO Posts (thread_id, content) VALUES (2, "Bye");
