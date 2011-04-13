package de.psi.alloy4smt.ui;

import java.awt.EventQueue;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JTextArea;

import de.psi.alloy4smt.ast.HyTranslator;
import de.psi.alloy4smt.hysat.HysatSolver;
import edu.mit.csail.sdg.alloy4.Err;

public class MainWindow extends JFrame {
	
	private static final long serialVersionUID = 1L;
	
	private static final String sampleSpec = 
		"open util/intref\n" +
		"one sig A { x: Int }\n" +
		"fact { A.x > 4 and A.x < 9 }\n" +
		"pred show {}\n" +
		"run show\n";
	
	private JTextArea document;

	public MainWindow() {
		super("Alloy - HySAT Minifrontend");
		
		setLayout(new FlowLayout());
		
		document = new JTextArea(10, 40);
		document.setText(sampleSpec);
		
		JButton trbtn = new JButton("Translate");
		trbtn.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				try {
					HysatSolver solver = new HysatSolver();
					HyTranslator.execute(document.getText(), solver);
					JOptionPane.showMessageDialog(null, "Translation successful. File is in " + solver.getHysatFile(), "Success", JOptionPane.INFORMATION_MESSAGE);
				} catch (Err ex) {
					JOptionPane.showMessageDialog(null, "Translation failed :(\n" + ex.msg, "Translation failed", JOptionPane.ERROR_MESSAGE);
				}
			}
		});
		
		add(document);
		add(trbtn);
		pack();
		
		setDefaultCloseOperation(DISPOSE_ON_CLOSE);
	}
	
	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			@Override
			public void run() {
				MainWindow wnd = new MainWindow();
				wnd.setVisible(true);
			}
		});
	}
}
